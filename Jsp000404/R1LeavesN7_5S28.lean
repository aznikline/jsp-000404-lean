import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S27

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11640000 in
set_option maxHeartbeats 11640000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s15 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  rcases m.htr 0 1 5 (by decide) (by decide) with h11282 | h11282
  · rcases m.htr 0 2 3 (by decide) (by decide) with h11283 | h11283
    · rcases m.htr 0 2 4 (by decide) (by decide) with h11284 | h11284
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11285 | h11285
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11286 | h11286
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11287 | h11287
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11288 | h11288
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11289 | h11289
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11290 | h11290
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11291 | h11291
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11292 | h11292
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11293 | h11293
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11294 | h11294
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11295 | h11295
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11296 | h11296
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11297 | h11297
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11298 | h11298
                                  · linarith only [h11283, h11295, h11298, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · linarith only [h11283, h11295, h11297, h11298, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11301 | h11301
                                  · linarith only [h11295, h11297, h11301, hlam]
                                  · rcases h0bigk with h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c | h11303c
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h0, hlam, p11303_1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h6310, hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h9935, hlam, p11303_1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11294, h11295, h11297, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11294, h11295, h11297, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11294, h11295, h11297, h6310, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11294, h11295, h11297, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11294, h11295, h11297, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11294, h11295, h11297, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo2]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11283, hlam, p11303_1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11283, h11294, h11295, h11297, h9935, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11283, h11294, h11295, h11297, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11294, h11295, h11297, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo3]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11284, hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11286, hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, h11283, h11286, h11294, h11295, h11297, hc34, hlam, hphi, ht0b, ht45, ht5b, p11303_1, u0elo1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11282, hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11285, hlam, p11303_1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11287, hlam, p11303_0]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [h11288, hlam, p11303_1]
                                    · have p11303_0 := h11303c.1
                                      have p11303_1 := h11303c.2.1
                                      have p11303_2 := h11303c.2.2.1
                                      have p11303_3 := h11303c.2.2.2
                                      linarith only [hlam, p11303_0]
                              · linarith only [h11282, h11293, h11295, h11296, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11330 | h11330
                              · linarith only [h11283, h11286, h11295, h11330, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11332 | h11332
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11333 | h11333
                                  · rcases h0bigk with h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c | h11334c
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h0, hlam, p11334_1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h6310, hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h9935, hlam, p11334_1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11289, h11292, h11293, h11330, h9935, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11334_1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11293, h11330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11286, hc34, hlam, hphi, ht0b, ht45, ht5b, p11334_1, u0elo1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11293, h11330, h9935, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11293, h11330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11293, h11330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo2]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11283, hlam, p11334_1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11283, h11293, h11330, h9935, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11283, h11293, h11330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11293, h11330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo3]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11284, hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11286, hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, h11283, h11286, h11293, h11330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11334_1, u0elo1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11282, hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11285, hlam, p11334_1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11287, hlam, p11334_0]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [h11288, hlam, p11334_1]
                                    · have p11334_0 := h11334c.1
                                      have p11334_1 := h11334c.2.1
                                      have p11334_2 := h11334c.2.2.1
                                      have p11334_3 := h11334c.2.2.2
                                      linarith only [hlam, p11334_0]
                                  · linarith only [h11284, h11295, h11332, h11333, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11361 | h11361
                                  · linarith only [h11283, h11286, h11295, h11332, h11361, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · linarith only [h11282, h11294, h11295, h11361, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h11288, h11294, h9935, hlam]
                        · linarith only [h11283, h11287, h11293, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h11286, h11292, h6310, hlam]
                    · linarith only [h0, h11285, h11291, hlam]
                  · linarith only [h0, h11282, h11284, h11290, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h0, h11283, h11289, hlam]
              · linarith only [h11282, h11288, h9935, hlam]
            · linarith only [h11282, h11286, h11287, h9935, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11372 | h11372
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11373 | h11373
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11374 | h11374
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11375 | h11375
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11376 | h11376
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11377 | h11377
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11378 | h11378
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11379 | h11379
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11380 | h11380
                            · linarith only [h11283, h11286, h11380, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11382 | h11382
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11383 | h11383
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11384 | h11384
                                  · rcases h0bigk with h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c | h11385c
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h0, hlam, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h6310, hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h9935, hlam, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11286, h11374, h11377, h6310, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, hc15, hlam, hphi, ht0b, ht5b, p11385_1, u0elo1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, h11376, h11382, h11384, h6310, hc45, hlam, hphi, ht0b, ht5b, p11385_1, u0elo1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, h11286, h11376, h11382, h11384, h6310, hc45, hlam, hphi, ht0b, ht5b, p11385_1, u0elo1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      rcases p11385_3 (m.d 0 1) (by simp) with h11395 | h11395
                                      · linarith only [h0, h11395, hlam]
                                      · linarith only [h11282, h11395, hlam]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, h11286, h11374, h11376, h11377, h11382, h11384, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11283, hlam, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11286, hlam, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, h11286, h11374, h11376, h11377, h11382, h11384, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, h11376, h11382, h11384, hc45, hlam, hphi, ht0b, ht5b, p11385_1, u0elo3]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11284, hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, h11286, h11374, h11376, h11377, h11382, h11384, h6310, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      rcases p11385_3 (m.d 0 1) (by simp) with h11407 | h11407
                                      · linarith only [h11407, h9935, hlam]
                                      · linarith only [h11282, h11407, hlam]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11282, hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11285, hlam, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11372, hlam, p11385_0]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [h11373, hlam, p11385_1]
                                    · have p11385_0 := h11385c.1
                                      have p11385_1 := h11385c.2.1
                                      have p11385_2 := h11385c.2.2.1
                                      have p11385_3 := h11385c.2.2.2
                                      linarith only [hlam, p11385_0]
                                  · linarith only [h11282, h11286, h11373, h11376, h11382, h11384, h6310, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                                · linarith only [h11282, h11286, h11374, h11377, h11379, h11383, h6310, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h11286, h11372, h11374, h11377, h11382, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h11286, h11373, h11377, h11379, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h11282, h11286, h11376, h11377, h11378, h6310, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11420 | h11420
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11421 | h11421
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11422 | h11422
                            · linarith only [h11282, h11376, h11377, h11422, h6310, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11424 | h11424
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11425 | h11425
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11426 | h11426
                                  · rcases h0bigk with h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c | h11427c
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h0, hlam, p11427_1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h6310, hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h9935, hlam, p11427_1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, h11376, h11377, h11424, h11426, h6310, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11427_1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, h11376, h11424, h11426, hc45, hlam, hphi, ht0b, ht5b, p11427_1, u0elo1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, h11376, h11424, h11426, h6310, hc45, hlam, hphi, ht0b, ht5b, p11427_1, u0elo1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, h11376, h11424, h11426, h9935, hc45, hlam, hphi, ht0b, ht5b, p11427_1, u0elo1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      rcases p11427_3 (m.d 0 1) (by simp) with h11437 | h11437
                                      · linarith only [h0, h11437, hlam]
                                      · linarith only [h11282, h11437, hlam]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, h11376, h11424, h11426, hc45, hlam, hphi, ht0b, ht5b, p11427_1, u0elo2]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11283, hlam, p11427_1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11286, hlam, p11427_1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      rcases p11427_3 (m.d 0 1) (by simp) with h11444 | h11444
                                      · linarith only [h11444, h6310, hlam]
                                      · linarith only [h11282, h11444, hlam]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, h11376, h11424, h11426, hc45, hlam, hphi, ht0b, ht5b, p11427_1, u0elo3]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11284, hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, h11284, h11376, h11424, h11426, h6310, hc45, hlam, hphi, ht0b, ht5b, p11427_1, u0elo1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      rcases p11427_3 (m.d 0 1) (by simp) with h11451 | h11451
                                      · linarith only [h11451, h9935, hlam]
                                      · linarith only [h11282, h11451, hlam]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11282, hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11285, hlam, p11427_1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11372, hlam, p11427_0]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [h11373, hlam, p11427_1]
                                    · have p11427_0 := h11427c.1
                                      have p11427_1 := h11427c.2.1
                                      have p11427_2 := h11427c.2.2.1
                                      have p11427_3 := h11427c.2.2.2
                                      linarith only [hlam, p11427_0]
                                  · linarith only [h11377, h11426, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h11282, h11421, h11422, h11424, h11425, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h11372, h11377, h11424, h6310, hc23, hc34, hlam, hphi]
                          · linarith only [h11373, h11421, h9935, hlam]
                        · linarith only [h11372, h11420, h6310, hlam]
                    · linarith only [h0, h11285, h11376, hlam]
                  · linarith only [h0, h11284, h11375, hlam]
                · linarith only [h0, h11283, h11374, hlam]
              · linarith only [h11282, h11286, h11373, h6310, hlam]
            · linarith only [h11282, h11372, h6310, hlam]
        · linarith only [h0, h11282, h11285, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11470 | h11470
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11471 | h11471
          · linarith only [h11283, h11284, h11471, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11473 | h11473
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11474 | h11474
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11475 | h11475
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11476 | h11476
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11477 | h11477
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11478 | h11478
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11479 | h11479
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11480 | h11480
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11481 | h11481
                            · linarith only [h11283, h11284, h11471, h11476, h11481, h6310, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11483 | h11483
                              · linarith only [h11283, h11284, h11475, h11478, h11481, h11483, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h11283, h11284, h11473, h11475, h11478, h11481, h11483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h11282, h11474, h11477, h11480, h9935, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h11283, h11284, h11471, h11478, h11479, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11488 | h11488
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11489 | h11489
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11490 | h11490
                            · linarith only [h11283, h11478, h11490, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11492 | h11492
                              · linarith only [h11283, h11284, h11476, h11492, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h11283, h11284, h11473, h11476, h11492, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h11283, h11284, h11476, h11489, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h11282, h11283, h11284, h11473, h11476, h11477, h11488, h6310, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h11284, h11476, h11477, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11498 | h11498
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11499 | h11499
                      · linarith only [h11471, h11475, h11476, h11499, h6310, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11501 | h11501
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11502 | h11502
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11503 | h11503
                            · linarith only [h11283, h11284, h11499, h11503, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11505 | h11505
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11506 | h11506
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11507 | h11507
                                  · rcases h0bigk with h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c | h11508c
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [hlam, p11508_0]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h0, hlam, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h6310, hlam, p11508_0]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h9935, hlam, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11475, h11476, h11503, h6310, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h0, h11476, h11503, hc01, hc34, hlam, hphi, ht12, ht23, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [hlam, p11508_0]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h0, h11282, h11476, h11498, h11503, h11505, h11507, h6310, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11284, hlam, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      rcases p11508_3 (m.d 0 1) (by simp) with h11518 | h11518
                                      · linarith only [h0, h11518, hlam]
                                      · linarith only [h11282, h11518, hlam]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11282, h11498, h11505, h11507, hc45, hlam, hphi, ht0b, ht5b, p11508_1, u0elo2]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11283, hlam, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [hlam, p11508_0]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11471, hlam, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      rcases p11508_3 (m.d 0 1) (by simp) with h11525 | h11525
                                      · linarith only [h11525, h6310, hlam]
                                      · linarith only [h11282, h11525, hlam]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11282, h11498, h11505, h11507, hc45, hlam, hphi, ht0b, ht5b, p11508_1, u0elo3]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11283, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11508_1, u0elo3]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11282, h11498, h11505, h11507, h6310, hc45, hlam, hphi, ht0b, ht5b, p11508_1, u0elo3]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [hlam, p11508_0]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      rcases p11508_3 (m.d 0 1) (by simp) with h11532 | h11532
                                      · linarith only [h11532, h9935, hlam]
                                      · linarith only [h11282, h11532, hlam]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11282, hlam, p11508_0]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11470, hlam, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11473, hlam, p11508_0]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [h11474, hlam, p11508_1]
                                    · have p11508_0 := h11508c.1
                                      have p11508_1 := h11508c.2.1
                                      have p11508_2 := h11508c.2.2.1
                                      have p11508_3 := h11508c.2.2.2
                                      linarith only [hlam, p11508_0]
                                  · linarith only [h11282, h11475, h11476, h11498, h11503, h11505, h11507, h6310, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h11282, h11475, h11476, h11502, h11506, h6310, hlam]
                              · linarith only [h11473, h11475, h11476, h11503, h11505, h6310, hc23, hc34, hlam, hphi]
                          · linarith only [h11474, h11502, h9935, hlam]
                        · linarith only [h11283, h11473, h11501, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h11470, h11498, hlam]
                · linarith only [h0, h11283, h11475, hlam]
              · linarith only [h0, h11282, h11284, h11474, hlam]
            · linarith only [h11282, h11473, h6310, hlam]
        · linarith only [h11282, h11283, h11470, h6310, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h11550 | h11550
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11551 | h11551
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11552 | h11552
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11553 | h11553
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11554 | h11554
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11555 | h11555
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11556 | h11556
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11557 | h11557
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11558 | h11558
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11559 | h11559
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11560 | h11560
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11561 | h11561
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11562 | h11562
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11563 | h11563
                                · linarith only [h11283, h11550, h11555, h11563, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h11283, h11550, h11554, h11555, h11563, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h11283, h11553, h11562, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h11283, h11552, h11561, hlam]
                          · linarith only [h11282, h11550, h11554, h11557, h11560, h9935, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h11283, h11553, h11555, h11559, hlam]
                      · linarith only [h11283, h11550, h11552, h11555, h11558, hlam]
                    · linarith only [h11283, h11551, h11557, hc12, hc23, hlam, hphi]
                  · linarith only [h11283, h11550, h11555, h11556, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11573 | h11573
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11574 | h11574
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11575 | h11575
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11576 | h11576
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11577 | h11577
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11578 | h11578
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11579 | h11579
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11580 | h11580
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11581 | h11581
                                  · rcases h0bigk with h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c | h11582c
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h0, hlam, p11582_1]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h6310, hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h9935, hlam, p11582_1]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h0, h11555, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11582_1]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h0, h11555, hc01, hc23, hlam, hphi, ht12, p11582_1]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11283, hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h0, h11282, h11555, h11574, h11579, h11581, h9935, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11582_1]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      rcases p11582_3 (m.d 0 1) (by simp) with h11592 | h11592
                                      · linarith only [h0, h11592, hlam]
                                      · linarith only [h11282, h11592, hlam]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11282, h11574, h11579, h11581, hc45, hlam, hphi, ht0b, ht5b, p11582_1, u0elo2]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h0, h11282, h11574, h11579, h11581, hc45, hlam, hphi, ht0b, ht5b, p11582_1, u0elo2]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11282, h11574, h11579, h11581, h9935, hc45, hlam, hphi, ht0b, ht5b, p11582_1, u0elo2]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      rcases p11582_3 (m.d 0 1) (by simp) with h11599 | h11599
                                      · linarith only [h11599, h6310, hlam]
                                      · linarith only [h11282, h11599, hlam]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11282, h11574, h11579, h11581, hc45, hlam, hphi, ht0b, ht5b, p11582_1, u0elo3]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11550, hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11552, hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      rcases p11582_3 (m.d 0 1) (by simp) with h11606 | h11606
                                      · linarith only [h11606, h9935, hlam]
                                      · linarith only [h11282, h11606, hlam]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11282, hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11551, hlam, p11582_1]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11553, hlam, p11582_0]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [h11554, hlam, p11582_1]
                                    · have p11582_0 := h11582c.1
                                      have p11582_1 := h11582c.2.1
                                      have p11582_2 := h11582c.2.2.1
                                      have p11582_3 := h11582c.2.2.2
                                      linarith only [hlam, p11582_0]
                                  · linarith only [h0, h11282, h11555, h11577, h11581, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h11282, h11555, h11573, h11577, h11580, h9935, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h11555, h11573, h11579, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h11282, h11555, h11573, h11577, h11578, h9935, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h11282, h11550, h11554, h11576, h11577, h9935, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h11553, h11576, h6310, hlam]
                      · linarith only [h11552, h11575, h6310, hlam]
                    · linarith only [h11551, h11573, h11574, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h11282, h11550, h11573, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h11282, h11554, h9935, hlam]
            · linarith only [h0, h11282, h11283, h11553, hlam]
          · linarith only [h11283, h11550, h11552, hlam]
        · linarith only [h11282, h11550, h11551, h9935, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11627 | h11627
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11628 | h11628
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11629 | h11629
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11630 | h11630
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11631 | h11631
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11632 | h11632
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11633 | h11633
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11634 | h11634
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11635 | h11635
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11636 | h11636
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11637 | h11637
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11638 | h11638
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11639 | h11639
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11640 | h11640
                                  · rcases h0bigk with h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h0, hlam, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h6310, hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h9935, hlam, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h0, h11282, h11283, h11631, h11633, h11638, h11640, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11550, h11632, hc01, hc14, hlam, hphi, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11283, hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11550, hlam, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11282, h11283, h11631, h11633, h11638, h11640, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11282, h11633, h11638, h11640, hc45, hlam, hphi, ht0b, ht5b, p11641_1, u0elo2]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h0, h11282, h11283, h11631, h11633, h11638, h11640, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11282, h11283, h11631, h11633, h11638, h11640, h9935, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      rcases p11641_3 (m.d 0 1) (by simp) with h11656 | h11656
                                      · linarith only [h11656, h6310, hlam]
                                      · linarith only [h11282, h11656, hlam]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11282, h11633, h11638, h11640, hc45, hlam, hphi, ht0b, ht5b, p11641_1, u0elo3]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h0, h11282, h11633, h11638, h11640, hc45, hlam, hphi, ht0b, ht5b, p11641_1, u0elo3]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11628, hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      rcases p11641_3 (m.d 0 1) (by simp) with h11663 | h11663
                                      · linarith only [h11663, h9935, hlam]
                                      · linarith only [h11282, h11663, hlam]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11282, hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11627, hlam, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11629, hlam, p11641_0]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [h11630, hlam, p11641_1]
                                    · have p11641_0 := h11641c.1
                                      have p11641_1 := h11641c.2.1
                                      have p11641_2 := h11641c.2.2.1
                                      have p11641_3 := h11641c.2.2.2
                                      linarith only [hlam, p11641_0]
                                  · linarith only [h0, h11282, h11283, h11631, h11636, h11640, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h11282, h11550, h11636, h11639, hlam]
                              · linarith only [h11283, h11629, h11638, hlam]
                            · linarith only [h11283, h11628, h11637, hlam]
                          · linarith only [h11628, h11630, h11636, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h11629, h11635, h6310, hlam]
                      · linarith only [h11283, h11628, h11631, h11634, hlam]
                    · linarith only [h0, h11627, h11633, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h11283, h11631, h11632, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11680 | h11680
                  · linarith only [h0, h11282, h11550, h11631, h11680, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11682 | h11682
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11683 | h11683
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11684 | h11684
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11685 | h11685
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11686 | h11686
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11687 | h11687
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11688 | h11688
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11689 | h11689
                                  · rcases h0bigk with h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c | h11690c
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h0, hlam, p11690_1]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h6310, hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h9935, hlam, p11690_1]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h0, h11680, h11686, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11690_1]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h0, h11680, h11686, hc01, hc23, hlam, hphi, ht12, p11690_1]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11283, hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11550, hlam, p11690_1]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      rcases p11690_3 (m.d 0 1) (by simp) with h11700 | h11700
                                      · linarith only [h0, h11700, hlam]
                                      · linarith only [h11282, h11700, hlam]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11282, h11682, h11687, h11689, hc45, hlam, hphi, ht0b, ht5b, p11690_1, u0elo2]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h0, h11282, h11682, h11687, h11689, hc45, hlam, hphi, ht0b, ht5b, p11690_1, u0elo2]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11282, h11682, h11687, h11689, h9935, hc45, hlam, hphi, ht0b, ht5b, p11690_1, u0elo2]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      rcases p11690_3 (m.d 0 1) (by simp) with h11707 | h11707
                                      · linarith only [h11707, h6310, hlam]
                                      · linarith only [h11282, h11707, hlam]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11282, h11682, h11687, h11689, hc45, hlam, hphi, ht0b, ht5b, p11690_1, u0elo3]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h0, h11282, h11682, h11687, h11689, hc45, hlam, hphi, ht0b, ht5b, p11690_1, u0elo3]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11628, hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      rcases p11690_3 (m.d 0 1) (by simp) with h11714 | h11714
                                      · linarith only [h11714, h9935, hlam]
                                      · linarith only [h11282, h11714, hlam]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11282, hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11627, hlam, p11690_1]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11629, hlam, p11690_0]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [h11630, hlam, p11690_1]
                                    · have p11690_0 := h11690c.1
                                      have p11690_1 := h11690c.2.1
                                      have p11690_2 := h11690c.2.2.1
                                      have p11690_3 := h11690c.2.2.2
                                      linarith only [hlam, p11690_0]
                                  · linarith only [h0, h11282, h11680, h11685, h11686, h11689, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h11282, h11680, h11685, h11688, hlam]
                              · linarith only [h0, h11680, h11686, h11687, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h11628, h11631, h11686, h6310, hlam]
                          · linarith only [h0, h11628, h11630, h11680, h11685, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h11629, h11684, h6310, hlam]
                      · linarith only [h11628, h11683, h6310, hlam]
                    · linarith only [h0, h11627, h11682, hlam]
              · linarith only [h0, h11282, h11550, h11630, hlam]
            · linarith only [h11282, h11629, h6310, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11732 | h11732
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11733 | h11733
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11734 | h11734
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11735 | h11735
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11736 | h11736
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11737 | h11737
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11738 | h11738
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11739 | h11739
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11740 | h11740
                            · linarith only [h0, h11283, h11628, h11734, h11740, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h11282, h11283, h11737, h11738, h11740, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h11282, h11733, h11738, h11739, h9935, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                        · linarith only [h11732, h11738, h6310, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11745 | h11745
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11746 | h11746
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11747 | h11747
                            · linarith only [h11734, h11737, h11747, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11749 | h11749
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11750 | h11750
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11751 | h11751
                                  · rcases h0bigk with h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c | h11752c
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h0, hlam, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h6310, hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h9935, hlam, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h0, h11283, h11734, h11737, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11283, h11734, hc01, hc13, hlam, hphi, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11283, hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11550, hlam, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11282, h11283, h11734, h11736, h11737, h11749, h11751, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11282, h11283, h11734, h11736, h11737, h11749, h11751, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11283, h11734, h11737, hc02, hc34, hlam, hphi, ht23, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11628, hlam, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      rcases p11752_3 (m.d 0 1) (by simp) with h11767 | h11767
                                      · linarith only [h11767, h6310, hlam]
                                      · linarith only [h11282, h11767, hlam]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11282, h11550, h11735, h11736, h11749, h11751, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h0, h11282, h11550, h11735, h11736, h11749, h11751, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11282, h11550, h11735, h11736, h11749, h11751, h6310, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      rcases p11752_3 (m.d 0 1) (by simp) with h11774 | h11774
                                      · linarith only [h11774, h9935, hlam]
                                      · linarith only [h11282, h11774, hlam]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11282, hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11627, hlam, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11732, hlam, p11752_0]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [h11733, hlam, p11752_1]
                                    · have p11752_0 := h11752c.1
                                      have p11752_1 := h11752c.2.1
                                      have p11752_2 := h11752c.2.2.1
                                      have p11752_3 := h11752c.2.2.2
                                      linarith only [hlam, p11752_0]
                                  · linarith only [h11737, h11751, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h11282, h11283, h11550, h11734, h11737, h11746, h11750, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h11283, h11732, h11749, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h11283, h11733, h11734, h11737, h11746, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h11282, h11283, h11732, h11734, h11736, h11745, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h11282, h11627, h11736, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h0, h11282, h11283, h11734, h11735, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11789 | h11789
                  · linarith only [h0, h11282, h11550, h11734, h11789, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11791 | h11791
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11792 | h11792
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11793 | h11793
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11794 | h11794
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11795 | h11795
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h11796 | h11796
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h11797 | h11797
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h11798 | h11798
                                  · rcases h0bigk with h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c | h11799c
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h0, hlam, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h6310, hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h9935, hlam, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h0, h11282, h11789, h11791, h11795, h11796, h11798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h0, h11789, h11795, hc01, hc23, hlam, hphi, ht12, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11283, hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11550, hlam, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11282, h11283, h11628, h11734, h11791, h11792, h11796, h11798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11282, h11628, h11734, h11791, h11792, h11796, h11798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11628, h11734, h11792, hc02, hc23, hlam, hphi, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11628, hlam, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11282, h11628, h11734, h11791, h11792, h11796, h11798, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11282, h11791, h11796, h11798, hc45, hlam, hphi, ht0b, ht5b, p11799_1, u0elo3]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h0, h11282, h11791, h11796, h11798, hc45, hlam, hphi, ht0b, ht5b, p11799_1, u0elo3]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11282, h11628, h11734, h11791, h11792, h11796, h11798, h6310, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      rcases p11799_3 (m.d 0 1) (by simp) with h11819 | h11819
                                      · linarith only [h11819, h9935, hlam]
                                      · linarith only [h11282, h11819, hlam]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11282, hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11627, hlam, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11732, hlam, p11799_0]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [h11733, hlam, p11799_1]
                                    · have p11799_0 := h11799c.1
                                      have p11799_1 := h11799c.2.1
                                      have p11799_2 := h11799c.2.2.1
                                      have p11799_3 := h11799c.2.2.2
                                      linarith only [hlam, p11799_0]
                                  · linarith only [h0, h11283, h11628, h11733, h11798, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h0, h11282, h11789, h11794, h11797, hlam]
                              · linarith only [h0, h11283, h11628, h11734, h11792, h11796, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h11734, h11792, h11795, hlam]
                          · linarith only [h11628, h11733, h11792, h11794, hlam]
                        · linarith only [h0, h11282, h11283, h11628, h11791, h11792, h11793, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11833 | h11833
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h11834 | h11834
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h11835 | h11835
                            · linarith only [h0, h11282, h11734, h11791, h11792, h11835, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h11282, h11734, h11791, h11835, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h11733, h11834, h9935, hlam]
                        · linarith only [h0, h11282, h11732, h11734, h11791, h11833, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h11282, h11627, h11791, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h0, h11282, h11283, h11628, h11733, hlam]
            · linarith only [h0, h11282, h11283, h11732, hlam]
        · linarith only [h0, h11282, h11627, hlam]
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16 m hb0 hb1 hb3 hb4 h0 h6310 h9935 h11282

set_option maxHeartbeats 14334000 in
set_option maxHeartbeats 14334000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s14_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h9935 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h9936 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h9937 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h9938 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h9939 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9940 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9941 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9942 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  rcases m.htr 1 2 3 (by decide) (by decide) with h9943 | h9943
  · rcases m.htr 1 2 4 (by decide) (by decide) with h9944 | h9944
    · rcases m.htr 1 2 5 (by decide) (by decide) with h9945 | h9945
      · rcases m.htr 1 3 4 (by decide) (by decide) with h9946 | h9946
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9947 | h9947
          · rcases m.htr 1 4 5 (by decide) (by decide) with h9948 | h9948
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9949 | h9949
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9950 | h9950
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9951 | h9951
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9952 | h9952
                    · linarith only [h9937, h9949, h9952, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h6310, h9935, h9937, h9948, h9952, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h6310, h9935, h9937, h9948, h9951, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h6310, h9935, h9937, h9947, h9948, h9949, h9950, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9957 | h9957
                · linarith only [h9937, h9940, h9949, h9957, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9959 | h9959
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9960 | h9960
                    · rcases h0bigk with h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c | h9961c
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h0, hlam, p9961_1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h6310, hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h6310, h9935, h9937, h9947, h9948, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h6310, h9936, h9937, h9947, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9935, h9947, h9948, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h6310, h9935, h9947, h9948, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9935, h9947, h9948, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9936, h9947, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9935, h9947, h9948, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo2]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9937, hlam, p9961_1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9935, h9937, h9947, h9948, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9936, h9937, h9947, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9935, hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9938, hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9940, hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9936, h9947, h9957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9961_1, u0elo3]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9936, hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9939, hlam, p9961_1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9941, hlam, p9961_0]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [h9942, hlam, p9961_1]
                      · have p9961_0 := h9961c.1
                        have p9961_1 := h9961c.2.1
                        have p9961_2 := h9961c.2.2.1
                        have p9961_3 := h9961c.2.2.2
                        linarith only [hlam, p9961_0]
                    · linarith only [h9938, h9959, h9960, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h6310, h9935, h9943, h9948, h9959, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9989 | h9989
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9990 | h9990
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9991 | h9991
                  · linarith only [h9938, h9948, h9991, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9993 | h9993
                    · linarith only [h9944, h9948, h9989, h9993, hlam]
                    · rcases h0bigk with h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c | h9995c
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h0, hlam, p9995_1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h6310, hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h6310, h9942, h9943, h9944, h9948, h9989, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9995_1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h6310, h9942, h9943, h9944, h9948, h9989, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9995_1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9935, h9944, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h6310, h9935, h9944, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9942, h9944, h9948, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9942, h9944, h9948, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9935, h9942, h9944, h9948, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo2]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9937, hlam, p9995_1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9937, h9942, h9944, h9948, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9937, h9942, h9944, h9948, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9935, hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9938, hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9940, hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9935, h9942, h9944, h9948, h9989, hc34, hlam, hphi, ht0b, ht45, ht5b, p9995_1, u0elo0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9936, hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9939, hlam, p9995_1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9941, hlam, p9995_0]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [h9942, hlam, p9995_1]
                      · have p9995_0 := h9995c.1
                        have p9995_1 := h9995c.2.1
                        have p9995_2 := h9995c.2.2.1
                        have p9995_3 := h9995c.2.2.2
                        linarith only [hlam, p9995_0]
                · linarith only [h6310, h9935, h9942, h9943, h9947, h9948, h9989, h9990, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h6310, h9935, h9942, h9943, h9946, h9948, h9989, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h6310, h9941, h9947, hlam]
        · linarith only [h6310, h9940, h9946, hlam]
      · linarith only [h0, h9939, h9945, hlam]
    · linarith only [h0, h9938, h9944, hlam]
  · linarith only [h0, h9937, h9943, hlam]

end R2N4
