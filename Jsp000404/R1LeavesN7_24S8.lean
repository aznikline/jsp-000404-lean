import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S4
import Jsp000404.R1LeavesN7_24S6
import Jsp000404.R1LeavesN7_24S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4426 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5051 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h5286 | h5286
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5287 | h5287
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5288 | h5288
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5289 | h5289
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5290 | h5290
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5291 | h5291
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5292 | h5292
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5293 | h5293
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5294 | h5294
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5295 | h5295
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5296 | h5296
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5297 | h5297
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5298 | h5298
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5299 | h5299
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5300 | h5300
                              · rcases h0bigk with h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c | h5301c
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h0, hlam, p5301_1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h3363, hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h4426, hlam, p5301_1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h5051, hlam, p5301_1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  rcases p5301_3 (m.d 0 1) (by simp) with h5307 | h5307
                                  · linarith only [h0, h5307, hlam]
                                  · rcases p5301_3 (m.d 0 2) (by simp) with h5309 | h5309
                                    · rcases p5301_3 (m.d 0 3) (by simp) with h5310 | h5310
                                      · linarith only [h5286, h5310, hlam]
                                      · linarith only [h3363, h5310, hlam]
                                    · linarith only [h0, h5309, hlam]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h0, h5286, h5297, h5300, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5301_1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  rcases p5301_3 (m.d 0 1) (by simp) with h5316 | h5316
                                  · linarith only [h0, h5316, hlam]
                                  · rcases p5301_3 (m.d 0 2) (by simp) with h5318 | h5318
                                    · rcases p5301_3 (m.d 0 3) (by simp) with h5319 | h5319
                                      · linarith only [h5286, h5319, hlam]
                                      · linarith only [h5289, h5319, hlam]
                                    · linarith only [h5287, h5318, hlam]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  rcases p5301_3 (m.d 0 1) (by simp) with h5323 | h5323
                                  · linarith only [h0, h5323, hlam]
                                  · rcases p5301_3 (m.d 0 2) (by simp) with h5325 | h5325
                                    · rcases p5301_3 (m.d 0 3) (by simp) with h5326 | h5326
                                      · linarith only [h5286, h5326, hlam]
                                      · linarith only [h5290, h5326, hlam]
                                    · linarith only [h5288, h5325, hlam]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p5301_1, u3elo0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h5286, hlam, p5301_1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h3363, h4426, hc01, hlam, hphi, ht12, ht23, p5301_1, u3elo1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h3363, h5051, hc01, hlam, hphi, ht12, ht23, p5301_1, u3elo1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h4426, h5295, hc01, hlam, hphi, ht12, ht23, p5301_1, u3elo1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h5287, hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h5289, hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h4426, h5051, h5295, hc01, hlam, hphi, ht12, ht23, p5301_1, u3elo1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h3363, h5290, hc01, hlam, hphi, ht12, ht23, p5301_1, u3elo1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h5288, hlam, p5301_1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h5290, hlam, p5301_0]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [h5291, hlam, p5301_1]
                                · have p5301_0 := h5301c.1
                                  have p5301_1 := h5301c.2.1
                                  have p5301_2 := h5301c.2.2.1
                                  have p5301_3 := h5301c.2.2.2
                                  linarith only [hlam, p5301_0]
                              · rcases h0bigk with h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c | h5345c
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h0, hlam, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h3363, hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h4426, hlam, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h5051, hlam, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  rcases p5345_3 (m.d 0 1) (by simp) with h5351 | h5351
                                  · linarith only [h0, h5351, hlam]
                                  · rcases p5345_3 (m.d 0 2) (by simp) with h5353 | h5353
                                    · rcases p5345_3 (m.d 0 3) (by simp) with h5354 | h5354
                                      · linarith only [h5286, h5354, hlam]
                                      · linarith only [h3363, h5354, hlam]
                                    · linarith only [h0, h5353, hlam]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h0, h5286, h5297, h5299, h5300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h0, h5287, h5299, h5300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  rcases p5345_3 (m.d 0 1) (by simp) with h5361 | h5361
                                  · linarith only [h0, h5361, hlam]
                                  · rcases p5345_3 (m.d 0 2) (by simp) with h5363 | h5363
                                    · rcases p5345_3 (m.d 0 3) (by simp) with h5364 | h5364
                                      · linarith only [h5286, h5364, hlam]
                                      · linarith only [h5290, h5364, hlam]
                                    · linarith only [h5288, h5363, hlam]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h3363, hc01, hlam, hphi, ht12, ht23, p5345_1, u3elo1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h5286, hlam, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h3363, h5287, h5299, h5300, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5345_1, u3elo1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h3363, h5051, hc01, hlam, hphi, ht12, ht23, p5345_1, u3elo1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h4426, h5295, hc01, hlam, hphi, ht12, ht23, p5345_1, u3elo1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h5287, hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h5289, hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h4426, h5051, h5295, hc01, hlam, hphi, ht12, ht23, p5345_1, u3elo1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h3363, h5290, hc01, hlam, hphi, ht12, ht23, p5345_1, u3elo1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h5288, hlam, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h5290, hlam, p5345_0]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [h5291, hlam, p5345_1]
                                · have p5345_0 := h5345c.1
                                  have p5345_1 := h5345c.2.1
                                  have p5345_2 := h5345c.2.2.1
                                  have p5345_3 := h5345c.2.2.2
                                  linarith only [hlam, p5345_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5383 | h5383
                              · linarith only [h3363, h5289, h5299, h5383, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases h0bigk with h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h0, hlam, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h3363, hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h4426, hlam, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h5051, hlam, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  rcases p5385_3 (m.d 0 1) (by simp) with h5391 | h5391
                                  · linarith only [h0, h5391, hlam]
                                  · rcases p5385_3 (m.d 0 2) (by simp) with h5393 | h5393
                                    · rcases p5385_3 (m.d 0 3) (by simp) with h5394 | h5394
                                      · linarith only [h5286, h5394, hlam]
                                      · linarith only [h3363, h5394, hlam]
                                    · linarith only [h0, h5393, hlam]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h0, h5289, h5291, h5297, h5299, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h0, h5291, h5297, h5299, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  rcases p5385_3 (m.d 0 1) (by simp) with h5401 | h5401
                                  · linarith only [h0, h5401, hlam]
                                  · rcases p5385_3 (m.d 0 2) (by simp) with h5403 | h5403
                                    · rcases p5385_3 (m.d 0 3) (by simp) with h5404 | h5404
                                      · linarith only [h5286, h5404, hlam]
                                      · linarith only [h5290, h5404, hlam]
                                    · linarith only [h5288, h5403, hlam]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p5385_1, u3elo0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h5286, hlam, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h3363, h5291, h5297, h5299, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5385_1, u3elo1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h3363, h5051, hc01, hlam, hphi, ht12, ht23, p5385_1, u3elo1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h4426, h5295, hc01, hlam, hphi, ht12, ht23, p5385_1, u3elo1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h5287, hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h5289, hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h4426, h5051, h5295, hc01, hlam, hphi, ht12, ht23, p5385_1, u3elo1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h3363, h5290, hc01, hlam, hphi, ht12, ht23, p5385_1, u3elo1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h5288, hlam, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h5290, hlam, p5385_0]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [h5291, hlam, p5385_1]
                                · have p5385_0 := h5385c.1
                                  have p5385_1 := h5385c.2.1
                                  have p5385_2 := h5385c.2.2.1
                                  have p5385_3 := h5385c.2.2.2
                                  linarith only [hlam, p5385_0]
                          · linarith only [h3363, h5290, h5298, hc23, hlam, hphi, u3elo1]
                        · linarith only [h3363, h5289, h5297, hc23, hlam, hphi, u3elo1]
                      · linarith only [h3363, h5290, h5296, hlam]
                    · linarith only [h3363, h5289, h5295, hlam]
                  · linarith only [h0, h5287, h5288, h5291, h5294, hlam]
                · linarith only [h0, h5287, h5293, hlam]
              · linarith only [h0, h5292, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5430 | h5430
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5431 | h5431
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5432 | h5432
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5433 | h5433
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5434 | h5434
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5435 | h5435
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5436 | h5436
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5437 | h5437
                            · linarith only [h0, h4426, h5286, h5291, h5435, h5437, hc01, hc12, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5439 | h5439
                              · linarith only [h3363, h5051, h5289, h5291, h5439, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases h0bigk with h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h0, hlam, p5441_1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h3363, hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h4426, hlam, p5441_1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5051, hlam, p5441_1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  rcases p5441_3 (m.d 0 1) (by simp) with h5447 | h5447
                                  · linarith only [h0, h5447, hlam]
                                  · rcases p5441_3 (m.d 0 2) (by simp) with h5449 | h5449
                                    · rcases p5441_3 (m.d 0 3) (by simp) with h5450 | h5450
                                      · linarith only [h5286, h5450, hlam]
                                      · linarith only [h3363, h5450, hlam]
                                    · linarith only [h0, h5449, hlam]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  rcases p5441_3 (m.d 0 1) (by simp) with h5455 | h5455
                                  · linarith only [h0, h5455, hlam]
                                  · rcases p5441_3 (m.d 0 2) (by simp) with h5457 | h5457
                                    · rcases p5441_3 (m.d 0 3) (by simp) with h5458 | h5458
                                      · linarith only [h5286, h5458, hlam]
                                      · rcases p5441_3 (m.d 0 4) (by simp) with h5460 | h5460
                                        · linarith only [h5287, h5460, hlam]
                                        · rcases p5441_3 (m.d 0 5) (by simp) with h5462 | h5462
                                          · linarith only [h5288, h5462, hlam]
                                          · rcases h0emin with h5464 | h5464 | h5464 | h5464 | h5464
                                            · linarith only [h5051, h5464, hc15, hlam, ht01]
                                            · rcases h2bigk with h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h0, hlam, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                rcases p5466_3 (m.d 0 2) (by simp) with h5469 | h5469
                                                · rcases p5466_3 (m.d 1 2) (by simp) with h5470 | h5470
                                                  · rcases p5466_3 (m.d 2 3) (by simp) with h5471 | h5471
                                                    · linarith only [h5471, hlam, p5466_0]
                                                    · rcases p5466_3 (m.d 2 4) (by simp) with h5473 | h5473
                                                      · linarith only [h5287, h5473, hlam]
                                                      · rcases p5466_3 (m.d 2 5) (by simp) with h5475 | h5475
                                                        · linarith only [h5288, h5475, hlam]
                                                        · rcases h2emin with h5477 | h5477 | h5477 | h5477 | h5477
                                                          · rcases h3bigk with h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c | h5478c
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h3363, hlam, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h0, h5436, h5439, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h0, h5439, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h4426, h5290, h5291, hc01, hlam, hphi, ht12, ht23, p5478_1, u3elo1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5436, h5439, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5478_1, u3elo1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              rcases p5478_3 (m.d 0 3) (by simp) with h5487 | h5487
                                                              · linarith only [h3363, h5487, hlam]
                                                              · linarith only [h5289, h5487, hlam]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              rcases p5478_3 (m.d 0 3) (by simp) with h5490 | h5490
                                                              · linarith only [h3363, h5490, hlam]
                                                              · linarith only [h5290, h5490, hlam]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5286, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5430, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5286, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5441_1, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h0, h5286, h5439, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5289, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5433, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5435, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5439, hlam, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5290, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5434, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h5436, hlam, p5478_0]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [h0, h5290, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5478_1]
                                                            · have p5478_0 := h5478c.1
                                                              have p5478_1 := h5478c.2.1
                                                              have p5478_2 := h5478c.2.2.1
                                                              have p5478_3 := h5478c.2.2.2
                                                              linarith only [hlam, p5478_0]
                                                          · rcases h3bigk with h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c | h5508c
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h3363, hlam, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5441_1, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5441_1, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [hc03, hlam, hphi, p5508_1, u3elo1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5436, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5508_1, u3elo1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              rcases p5508_3 (m.d 0 3) (by simp) with h5517 | h5517
                                                              · linarith only [h3363, h5517, hlam]
                                                              · linarith only [h5289, h5517, hlam]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              rcases p5508_3 (m.d 0 3) (by simp) with h5520 | h5520
                                                              · linarith only [h3363, h5520, hlam]
                                                              · linarith only [h5290, h5520, hlam]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5286, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5430, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5466_1, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h0, h5286, h5439, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5289, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5433, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5435, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5439, hlam, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5290, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5434, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h5436, hlam, p5508_0]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [h0, h5290, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5508_1]
                                                            · have p5508_0 := h5508c.1
                                                              have p5508_1 := h5508c.2.1
                                                              have p5508_2 := h5508c.2.2.1
                                                              have p5508_3 := h5508c.2.2.2
                                                              linarith only [hlam, p5508_0]
                                                          · linarith only [h0, h5286, h5477, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5441_1]
                                                          · linarith only [h4426, h5287, h5433, h5477, hlam, ht23, u3elo1]
                                                          · linarith only [h5051, h5288, h5434, h5477, hlam, ht23, u3elo1]
                                                  · linarith only [h5430, h5470, hlam]
                                                · linarith only [h5469, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                rcases p5466_3 (m.d 0 2) (by simp) with h5543 | h5543
                                                · rcases p5466_3 (m.d 1 2) (by simp) with h5544 | h5544
                                                  · rcases p5466_3 (m.d 2 3) (by simp) with h5545 | h5545
                                                    · linarith only [h5286, h5545, hlam]
                                                    · linarith only [h5435, h5545, hlam]
                                                  · linarith only [h5431, h5544, hlam]
                                                · linarith only [h5543, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                rcases p5466_3 (m.d 0 2) (by simp) with h5550 | h5550
                                                · rcases p5466_3 (m.d 1 2) (by simp) with h5551 | h5551
                                                  · rcases p5466_3 (m.d 2 3) (by simp) with h5552 | h5552
                                                    · linarith only [h5286, h5552, hlam]
                                                    · linarith only [h5436, h5552, hlam]
                                                  · linarith only [h5432, h5551, hlam]
                                                · linarith only [h5550, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5464, hc12, hlam, ht01, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                rcases p5466_3 (m.d 0 2) (by simp) with h5559 | h5559
                                                · linarith only [h0, h5559, hlam]
                                                · linarith only [h5286, h5559, hlam]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                rcases p5466_3 (m.d 0 2) (by simp) with h5562 | h5562
                                                · linarith only [h0, h5562, hlam]
                                                · linarith only [h5287, h5562, hlam]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                rcases p5466_3 (m.d 0 2) (by simp) with h5565 | h5565
                                                · linarith only [h0, h5565, hlam]
                                                · linarith only [h5288, h5565, hlam]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5286, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5430, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5286, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p5441_1, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h0, h5286, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5441_1, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5287, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5431, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5435, hlam, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5437, hlam, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5288, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5432, hlam, p5466_0]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h5436, hlam, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [h0, h5288, h5290, h5435, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5441_1, p5466_1]
                                              · have p5466_0 := h5466c.1
                                                have p5466_1 := h5466c.2.1
                                                have p5466_2 := h5466c.2.2.1
                                                have p5466_3 := h5466c.2.2.2
                                                linarith only [hlam, p5466_0]
                                            · linarith only [h0, h5464, hc12, hlam, ht01, p5441_1]
                                            · linarith only [h0, h5290, h5291, h5464, hc12, hlam, ht01, p5441_1]
                                            · linarith only [h0, h5290, h5464, hc12, hlam, ht01, p5441_1]
                                    · linarith only [h5286, h5457, hlam]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  rcases p5441_3 (m.d 0 1) (by simp) with h5587 | h5587
                                  · linarith only [h0, h5587, hlam]
                                  · rcases p5441_3 (m.d 0 2) (by simp) with h5589 | h5589
                                    · rcases p5441_3 (m.d 0 3) (by simp) with h5590 | h5590
                                      · linarith only [h5286, h5590, hlam]
                                      · linarith only [h5289, h5590, hlam]
                                    · linarith only [h5287, h5589, hlam]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  rcases p5441_3 (m.d 0 1) (by simp) with h5594 | h5594
                                  · linarith only [h0, h5594, hlam]
                                  · rcases p5441_3 (m.d 0 2) (by simp) with h5596 | h5596
                                    · rcases p5441_3 (m.d 0 3) (by simp) with h5597 | h5597
                                      · linarith only [h5286, h5597, hlam]
                                      · linarith only [h5290, h5597, hlam]
                                    · linarith only [h5288, h5596, hlam]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p5441_1, u3elo0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5286, hlam, p5441_1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h3363, h4426, hc01, hlam, hphi, ht12, ht23, p5441_1, u3elo1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h3363, h5051, hc01, hlam, hphi, ht12, ht23, p5441_1, u3elo1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h4426, h5433, hc01, hlam, hphi, ht12, ht23, p5441_1, u3elo1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5287, hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5289, hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5291, hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5051, h5434, hc01, hlam, hphi, ht12, ht23, p5441_1, u3elo1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5288, hlam, p5441_1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h5290, hlam, p5441_0]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [h4426, h5051, h5434, hc01, hlam, hphi, ht12, ht23, p5441_1, u3elo1]
                                · have p5441_0 := h5441c.1
                                  have p5441_1 := h5441c.2.1
                                  have p5441_2 := h5441c.2.2.1
                                  have p5441_3 := h5441c.2.2.2
                                  linarith only [hlam, p5441_0]
                          · linarith only [h3363, h5290, h5436, hc23, hlam, hphi, u3elo1]
                        · linarith only [h3363, h5289, h5435, hc23, hlam, hphi, u3elo1]
                      · linarith only [h3363, h5290, h5434, hlam]
                    · linarith only [h3363, h5433, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5288, h5432, hlam]
                · linarith only [h0, h5287, h5431, hlam]
              · linarith only [h0, h5430, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5623 | h5623
            · linarith only [h5289, h5290, h5623, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5625 | h5625
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5626 | h5626
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5627 | h5627
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5628 | h5628
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5629 | h5629
                      · linarith only [h5290, h5629, hc03, hlam, hphi, u3elo1]
                      · linarith only [h3363, h5629, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h3363, h5628, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5288, h5627, hlam]
                · linarith only [h0, h5287, h5626, hlam]
              · linarith only [h0, h5625, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5636 | h5636
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5637 | h5637
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5638 | h5638
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5639 | h5639
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5640 | h5640
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5641 | h5641
                    · linarith only [h5289, h5641, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5641, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5288, h5640, hlam]
                · linarith only [h0, h5287, h5639, hlam]
              · linarith only [h0, h5286, h5638, hlam]
            · linarith only [h5289, h5636, h5637, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5648 | h5648
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5649 | h5649
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5650 | h5650
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5651 | h5651
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5652 | h5652
                    · linarith only [h5289, h5652, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5652, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5288, h5651, hlam]
                · linarith only [h0, h5287, h5650, hlam]
              · linarith only [h0, h5286, h5649, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5658 | h5658
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5659 | h5659
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5660 | h5660
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5661 | h5661
                    · linarith only [h3363, h5289, h5661, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h5661, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5288, h5660, hlam]
                · linarith only [h0, h5287, h5659, hlam]
              · linarith only [h0, h5286, h5658, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5667 | h5667
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5668 | h5668
          · linarith only [h5286, h5288, h5668, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5670 | h5670
            · linarith only [h5287, h5288, h5670, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5672 | h5672
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5673 | h5673
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5674 | h5674
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5675 | h5675
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5676 | h5676
                      · linarith only [h4426, h5667, h5668, h5676, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h3363, h5676, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h3363, h5675, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5680 | h5680
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5681 | h5681
                      · linarith only [h5668, h5681, hc03, hlam, hphi, u3elo1]
                      · linarith only [h3363, h5681, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h3363, h5680, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h5287, h5673, hlam]
              · linarith only [h0, h5672, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5687 | h5687
          · linarith only [h5286, h5288, h5667, h5687, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5689 | h5689
            · linarith only [h5287, h5288, h5689, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5691 | h5691
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5692 | h5692
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5693 | h5693
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5694 | h5694
                    · linarith only [h5667, h5694, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5694, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5697 | h5697
                    · linarith only [h3363, h5667, h5697, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h5697, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h5287, h5692, hlam]
              · linarith only [h0, h5691, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5702 | h5702
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5703 | h5703
        · linarith only [h5286, h5287, h5703, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5705 | h5705
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5706 | h5706
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5707 | h5707
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5708 | h5708
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5709 | h5709
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5710 | h5710
                    · linarith only [h5703, h5710, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5710, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h5287, h5702, h5708, h5709, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5714 | h5714
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5715 | h5715
                    · linarith only [h5703, h5705, h5715, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h3363, h5715, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h5287, h5702, h5703, h5714, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h0, h5286, h5707, hlam]
            · linarith only [h5286, h5287, h5703, h5705, h5706, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5721 | h5721
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5722 | h5722
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5723 | h5723
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5724 | h5724
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5725 | h5725
                    · linarith only [h5703, h5725, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5725, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h5287, h5702, h5723, h5724, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5729 | h5729
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5730 | h5730
                    · linarith only [h3363, h5703, h5730, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h5730, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5702, h5729, hlam]
              · linarith only [h0, h5722, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h5287, h5702, h5721, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5736 | h5736
        · linarith only [h5286, h5287, h5736, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5738 | h5738
          · linarith only [h5286, h5702, h5736, h5738, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5740 | h5740
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5741 | h5741
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5742 | h5742
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5743 | h5743
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5744 | h5744
                    · linarith only [h5736, h5744, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5744, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h5286, h5287, h5742, h5743, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5748 | h5748
                  · linarith only [h5286, h5702, h5742, h5748, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5750 | h5750
                    · linarith only [h3363, h5736, h5750, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h5750, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h5741, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5754 | h5754
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5755 | h5755
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5756 | h5756
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5757 | h5757
                    · linarith only [h3363, h5736, h5757, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h5757, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h5286, h5287, h5755, h5756, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5761 | h5761
                  · linarith only [h5286, h5702, h5755, h5761, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5763 | h5763
                    · linarith only [h3363, h5736, h5763, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h5763, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h5754, hc01, hlam, hphi, ht12, ht23, u3elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5767 | h5767
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5768 | h5768
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5769 | h5769
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5770 | h5770
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5771 | h5771
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5772 | h5772
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5773 | h5773
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5774 | h5774
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5775 | h5775
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5776 | h5776
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5777 | h5777
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5778 | h5778
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5779 | h5779
                            · linarith only [h5286, h5767, h5772, h5779, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h5286, h5767, h5771, h5772, h5777, h5779, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h5286, h5778, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h5286, h5777, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h3363, h5776, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h5286, h5767, h5769, h5772, h5775, hlam]
                  · linarith only [h5286, h5768, h5772, h5774, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h5286, h5767, h5772, h5773, hlam]
              · linarith only [h0, h5772, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5789 | h5789
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5790 | h5790
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5791 | h5791
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5792 | h5792
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5793 | h5793
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5794 | h5794
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5795 | h5795
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5796 | h5796
                            · linarith only [h5286, h5767, h5771, h5789, h5796, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5798 | h5798
                              · linarith only [h4426, h5286, h5768, h5771, h5789, h5794, h5796, h5798, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases h0bigk with h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c | h5800c
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h0, hlam, p5800_1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h3363, hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h4426, hlam, p5800_1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5051, hlam, p5800_1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5286, h5789, hc01, hlam, hphi, ht12, ht23, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5286, hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h4426, h5286, h5789, hc01, hlam, hphi, ht12, ht23, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5286, h5789, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5286, h5789, hc01, hlam, hphi, ht12, ht23, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5286, h5789, hc02, hlam, hphi, ht23, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h4426, h5286, h5789, hc01, hlam, hphi, ht12, ht23, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5051, h5286, h5789, hc01, hlam, hphi, ht12, ht23, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5771, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5800_1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5767, hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5769, hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5771, hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5286, h5768, h5789, hc01, hlam, hphi, ht12, ht23, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5768, hlam, p5800_1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5770, hlam, p5800_0]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [h5286, h5768, h5789, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5800_1, u3elo1]
                                · have p5800_0 := h5800c.1
                                  have p5800_1 := h5800c.2.1
                                  have p5800_2 := h5800c.2.2.1
                                  have p5800_3 := h5800c.2.2.2
                                  linarith only [hlam, p5800_0]
                          · linarith only [h5286, h5795, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h5286, h5794, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h5286, h5768, h5770, h5793, hc13, hlam, hphi, u3elo2]
                    · linarith only [h5286, h5768, h5769, h5771, h5789, h5792, hlam]
                  · linarith only [h5286, h5768, h5789, h5791, hlam]
                · linarith only [h5286, h5767, h5789, h5790, hlam]
              · linarith only [h0, h5789, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h5286, h5768, h5770, hlam]
        · linarith only [h5286, h5767, h5769, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5835 | h5835
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5836 | h5836
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5837 | h5837
            · linarith only [h5767, h5768, h5837, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5839 | h5839
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5840 | h5840
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5841 | h5841
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5842 | h5842
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5843 | h5843
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5844 | h5844
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5845 | h5845
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5846 | h5846
                            · linarith only [h5767, h5768, h5837, h5846, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5848 | h5848
                              · linarith only [h5768, h5846, h5848, hc02, hlam, hphi, ht23, u3elo3]
                              · rcases h0bigk with h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c | h5850c
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h0, hlam, p5850_1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h3363, hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h4426, hlam, p5850_1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5051, hlam, p5850_1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5768, hc01, hc25, hlam, hphi, ht12, p5850_1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5286, hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h4426, h5286, h5839, hc01, hlam, hphi, ht12, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5768, hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5286, h5839, hc01, hlam, hphi, ht12, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5286, h5767, h5839, h5844, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h4426, h5286, h5839, hc01, hlam, hphi, ht12, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5051, h5286, h5839, hc01, hlam, hphi, ht12, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5286, h5767, h5839, hc01, hlam, hphi, ht12, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5767, hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5835, hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5837, hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5051, h5843, hc01, hlam, hphi, ht12, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5051, h5843, hc02, hlam, hphi, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h5836, hlam, p5850_0]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [h4426, h5286, h5836, h5839, hc01, hlam, hphi, ht12, ht23, p5850_1, u3elo1]
                                · have p5850_0 := h5850c.1
                                  have p5850_1 := h5850c.2.1
                                  have p5850_2 := h5850c.2.2.1
                                  have p5850_3 := h5850c.2.2.2
                                  linarith only [hlam, p5850_0]
                          · linarith only [h5286, h5836, h5845, hlam]
                        · linarith only [h5286, h5844, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h5836, h5843, hc13, hlam, hphi, u3elo0]
                    · linarith only [h5286, h5767, h5839, h5842, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h5286, h5767, h5839, h5841, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h5286, h5767, h5839, h5840, hlam]
              · linarith only [h0, h5839, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5883 | h5883
            · linarith only [h5767, h5768, h5883, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5885 | h5885
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5886 | h5886
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5887 | h5887
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5888 | h5888
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5889 | h5889
                      · linarith only [h5836, h5889, hc03, hlam, hphi, u3elo1]
                      · linarith only [h3363, h5889, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h5286, h5767, h5885, h5888, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h5286, h5767, h5885, h5887, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h5286, h5767, h5885, h5886, hlam]
              · linarith only [h0, h5885, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h5286, h5767, h5835, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5897 | h5897
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5898 | h5898
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5899 | h5899
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5900 | h5900
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5901 | h5901
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5902 | h5902
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5903 | h5903
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5904 | h5904
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5905 | h5905
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5906 | h5906
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5907 | h5907
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5908 | h5908
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5909 | h5909
                              · rcases h0bigk with h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h0, hlam, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h3363, hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h4426, hlam, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5051, hlam, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5767, h5902, hc01, hc14, hlam, hphi, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5286, hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5767, hlam, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5051, h5767, h5902, hc01, hc14, hlam, hphi, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p5910_1, u3elo0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5286, h5901, hc02, hlam, hphi, ht23, p5910_1, u3elo1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5286, h5767, h5897, h5901, h5907, h5909, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5910_1, u3elo1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5051, h5286, h5901, hc01, hlam, hphi, ht12, ht23, p5910_1, u3elo1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5286, h5898, h5901, hc01, hlam, hphi, ht12, ht23, p5910_1, u3elo1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5286, h5897, h5898, h5901, h5907, h5909, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5910_1, u3elo1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5898, hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5051, h5286, h5898, h5901, hc01, hlam, hphi, ht12, ht23, p5910_1, u3elo1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5286, h5897, h5901, hc01, hlam, hphi, ht12, ht23, p5910_1, u3elo1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5897, hlam, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5899, hlam, p5910_0]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [h5900, hlam, p5910_1]
                                · have p5910_0 := h5910c.1
                                  have p5910_1 := h5910c.2.1
                                  have p5910_2 := h5910c.2.2.1
                                  have p5910_3 := h5910c.2.2.2
                                  linarith only [hlam, p5910_0]
                              · linarith only [h5767, h5897, h5902, h5904, h5908, h5909, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h5286, h5767, h5898, h5900, h5901, h5908, hc02, hlam, hphi, ht23, u3elo1]
                          · linarith only [h5286, h5897, h5907, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h5286, h5897, h5906, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h5286, h5897, h5899, h5905, hc13, hlam, hphi, u3elo2]
                    · linarith only [h5286, h5898, h5901, h5904, hlam]
                  · linarith only [h5286, h5901, h5903, hc02, hc25, hlam, hphi]
                · linarith only [h5051, h5286, h5897, h5901, h5902, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h5901, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h5767, h5897, h5900, hlam]
          · linarith only [h5767, h5897, h5898, h5899, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5947 | h5947
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5948 | h5948
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5949 | h5949
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5950 | h5950
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5951 | h5951
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5952 | h5952
                    · linarith only [h5898, h5952, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5952, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h5286, h5897, h5949, h5951, hlam]
                · linarith only [h5286, h5897, h5949, h5950, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h5949, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h5286, h5897, h5898, h5948, hlam]
          · linarith only [h5286, h5897, h5947, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5960 | h5960
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5961 | h5961
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5962 | h5962
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5963 | h5963
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5964 | h5964
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5965 | h5965
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5966 | h5966
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5967 | h5967
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5968 | h5968
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5969 | h5969
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5970 | h5970
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5971 | h5971
                              · rcases h0bigk with h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h0, hlam, p5972_1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h3363, hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h4426, hlam, p5972_1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5051, hlam, p5972_1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5897, h5964, h5970, hc01, hc14, hlam, hphi, p5972_1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5286, hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5767, hlam, p5972_1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5897, hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5286, h5963, hc02, hlam, hphi, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h4426, h5286, h5963, hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h0, h5286, h5897, h5963, hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5286, h5960, h5963, hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h0, h5286, h5960, h5963, hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5960, hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5051, h5286, h5960, h5963, hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5286, h5961, h5963, hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h0, h5286, h5961, h5963, hc01, hlam, hphi, ht12, ht23, p5972_1, u3elo1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5961, hlam, p5972_0]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [h5962, hlam, p5972_1]
                                · have p5972_0 := h5972c.1
                                  have p5972_1 := h5972c.2.1
                                  have p5972_2 := h5972c.2.2.1
                                  have p5972_3 := h5972c.2.2.2
                                  linarith only [hlam, p5972_0]
                              · rcases h0bigk with h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h0, hlam, p5998_1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h3363, hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h4426, hlam, p5998_1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5051, hlam, p5998_1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5286, h5963, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5286, hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5767, hlam, p5998_1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5897, hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5286, h5963, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5286, h5963, hc02, hlam, hphi, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5286, h5962, h5963, h5971, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5051, h5286, h5963, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h4426, h5966, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h0, h5767, h5964, h5966, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5960, hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h0, h5767, h5897, h5964, h5966, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5897, h5964, h5966, h5970, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h0, h5897, h5964, h5966, h5970, hc01, hlam, hphi, ht12, ht23, p5998_1, u3elo1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5961, hlam, p5998_0]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [h5962, hlam, p5998_1]
                                · have p5998_0 := h5998c.1
                                  have p5998_1 := h5998c.2.1
                                  have p5998_2 := h5998c.2.2.1
                                  have p5998_3 := h5998c.2.2.2
                                  linarith only [hlam, p5998_0]
                            · linarith only [h0, h4426, h5767, h5962, h5966, h5970, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h0, h5286, h5969, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h5286, h5968, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h5961, h5967, hc13, hlam, hphi, u3elo0]
                    · linarith only [h5286, h5960, h5963, h5966, hlam]
                  · linarith only [h0, h5286, h5963, h5965, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h5286, h5963, h5964, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h5963, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6032 | h6032
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6033 | h6033
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6034 | h6034
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6035 | h6035
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6036 | h6036
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6037 | h6037
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6038 | h6038
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6039 | h6039
                            · linarith only [h4426, h5962, h6033, h6035, h6039, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6041 | h6041
                              · linarith only [h0, h5767, h6039, h6041, hc01, hlam, hphi, ht12, ht23, u3elo3]
                              · rcases h0bigk with h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c | h6043c
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h0, hlam, p6043_1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h3363, hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h4426, hlam, p6043_1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5051, hlam, p6043_1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5286, h6032, hc01, hlam, hphi, ht12, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5286, hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5767, hlam, p6043_1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5897, hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5286, h6032, hc01, hlam, hphi, ht12, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5286, h6032, hc02, hlam, hphi, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h4426, h5286, h6032, hc01, hlam, hphi, ht12, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5051, h5286, h6032, hc01, hlam, hphi, ht12, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5767, h6039, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6043_1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h0, h5767, h6039, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6043_1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5960, hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5962, hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5286, h5961, h6032, hc01, hlam, hphi, ht12, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h0, h5286, h5961, h6032, hc01, hlam, hphi, ht12, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h5961, hlam, p6043_0]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [h4426, h5286, h5961, h6032, hc01, hlam, hphi, ht12, ht23, p6043_1, u3elo1]
                                · have p6043_0 := h6043c.1
                                  have p6043_1 := h6043c.2.1
                                  have p6043_2 := h6043c.2.2.1
                                  have p6043_3 := h6043c.2.2.2
                                  linarith only [hlam, p6043_0]
                          · linarith only [h5286, h5961, h6038, hlam]
                        · linarith only [h0, h4426, h5286, h5960, h6035, h6037, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h5286, h5961, h6032, h6036, hlam]
                    · linarith only [h5286, h5960, h6032, h6035, hlam]
                  · linarith only [h0, h5286, h6032, h6034, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h5286, h6032, h6033, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h6032, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6076 | h6076
            · linarith only [h5960, h5961, h6076, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6078 | h6078
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6079 | h6079
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6080 | h6080
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6081 | h6081
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6082 | h6082
                      · linarith only [h5961, h6082, hc03, hlam, hphi, u3elo1]
                      · linarith only [h3363, h6082, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h5286, h6078, h6081, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5286, h6078, h6080, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h5286, h6078, h6079, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h6078, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6089 | h6089
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6090 | h6090
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6091 | h6091
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6092 | h6092
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6093 | h6093
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6094 | h6094
                    · linarith only [h5960, h6094, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h6094, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5286, h6091, h6093, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h5286, h6091, h6092, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h6091, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h5960, h6089, h6090, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6101 | h6101
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6102 | h6102
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6103 | h6103
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6104 | h6104
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6105 | h6105
                    · linarith only [h0, h5286, h5960, h6105, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h6105, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5286, h6102, h6104, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h5286, h6102, h6103, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h6102, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6111 | h6111
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6112 | h6112
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6113 | h6113
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6114 | h6114
                    · linarith only [h0, h5286, h5960, h6114, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h6114, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h5286, h6111, h6113, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h5286, h6111, h6112, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h6111, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4426 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h5051 | h5051
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x1_x0 m hb0 hb2 hb3 hg0 h3363 h4426 h5051
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x1_x1 m hb0 hb2 hb3 hg0 h3363 h4426 h5051

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h4426 | h4426
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x0 m hb0 hb2 hb3 hg0 h3363 h4426
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x1 m hb0 hb2 hb3 hg0 h3363 h4426

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h3363 | h3363
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0 m hb0 hb2 hb3 hg0 h3363
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x1 m hb0 hb2 hb3 hg0 h3363

set_option maxHeartbeats 12240000 in
set_option maxHeartbeats 12240000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5 m hb0 hb2 hb3 h0

end R2N4
