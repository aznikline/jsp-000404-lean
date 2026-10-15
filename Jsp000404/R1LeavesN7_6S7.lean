import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h218 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h287 | h287
  · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
    · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
      · rcases m.htr 1 2 5 (by decide) (by decide) with h290 | h290
        · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
          · linarith only [h1, h291, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
            · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
              · linarith only [h0, h288, h294, h7, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h296 | h296
                · linarith only [h0, h218, h289, h294, h296, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                  · linarith only [h0, h289, h298, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h2, h293, h298, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
              · linarith only [h2, h288, h291, h301, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                · linarith only [h218, h287, h288, h291, h293, h303, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                  · linarith only [h0, h288, h291, h293, h305, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                    · rcases h0bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1, u0elo0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        rcases p308_3 (m.d 0 1) (by simp) with h311 | h311
                        · rcases p308_3 (m.d 0 2) (by simp) with h312 | h312
                          · linarith only [h0, h312, hlam]
                          · linarith only [h312, h4, hlam]
                        · linarith only [h1, h311, hlam]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h287, h288, h291, h293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1, u0elo0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h287, h288, h291, h293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1, u0elo0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h0, hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        rcases p308_3 (m.d 0 1) (by simp) with h320 | h320
                        · rcases p308_3 (m.d 0 2) (by simp) with h321 | h321
                          · rcases p308_3 (m.d 0 3) (by simp) with h322 | h322
                            · linarith only [h322, h4, hlam]
                            · rcases p308_3 (m.d 0 4) (by simp) with h324 | h324
                              · linarith only [h324, h5, hlam]
                              · linarith only [h324, h7, hlam]
                          · linarith only [h321, h4, hlam]
                        · linarith only [h1, h320, hlam]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h287, h288, h291, h293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1, u0elo1]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h0, h287, h288, h291, h293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1, u0elo0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h1, hlam, p308_1]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h4, hlam, p308_1]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h7, hlam, p308_1]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h218, hlam, p308_1]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h2, hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h5, hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        rcases p308_3 (m.d 0 1) (by simp) with h338 | h338
                        · rcases p308_3 (m.d 0 2) (by simp) with h339 | h339
                          · rcases p308_3 (m.d 0 3) (by simp) with h340 | h340
                            · linarith only [h340, h7, hlam]
                            · rcases p308_3 (m.d 0 4) (by simp) with h342 | h342
                              · rcases p308_3 (m.d 0 5) (by simp) with h343 | h343
                                · linarith only [h287, h343, hlam]
                                · linarith only [h218, h343, hlam]
                              · linarith only [h342, h7, hlam]
                          · linarith only [h339, h4, hlam]
                        · linarith only [h1, h338, hlam]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h287, h288, h291, h293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1, u0elo3]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h3, hlam, p308_0]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h6, hlam, p308_1]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        rcases p308_3 (m.d 0 1) (by simp) with h353 | h353
                        · rcases p308_3 (m.d 0 2) (by simp) with h354 | h354
                          · rcases p308_3 (m.d 0 3) (by simp) with h355 | h355
                            · linarith only [h218, h355, hlam]
                            · rcases p308_3 (m.d 0 4) (by simp) with h357 | h357
                              · rcases p308_3 (m.d 0 5) (by simp) with h358 | h358
                                · rcases h0emin with h359 | h359 | h359 | h359 | h359
                                  · rcases h2bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, h288, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u0elo0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      rcases p360_3 (m.d 0 2) (by simp) with h363 | h363
                                      · rcases p360_3 (m.d 1 2) (by simp) with h364 | h364
                                        · linarith only [h0, h364, hlam]
                                        · linarith only [h288, h364, hlam]
                                      · linarith only [h363, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      rcases p360_3 (m.d 0 2) (by simp) with h368 | h368
                                      · rcases p360_3 (m.d 1 2) (by simp) with h369 | h369
                                        · linarith only [h0, h369, hlam]
                                        · linarith only [h289, h369, hlam]
                                      · linarith only [h368, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      rcases p360_3 (m.d 0 2) (by simp) with h373 | h373
                                      · rcases p360_3 (m.d 1 2) (by simp) with h374 | h374
                                        · linarith only [h0, h374, hlam]
                                        · linarith only [h290, h374, hlam]
                                      · linarith only [h373, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u0elo0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, h301, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u0elo0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, h301, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u0elo0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h4, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h288, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h301, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h303, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h5, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h289, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u0elo0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h305, hlam, p360_1]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h6, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h290, hlam, p360_0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, h290, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p360_1, u0elo0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [h0, h290, hc24, hlam, hphi, ht0b, ht45, ht5b, p360_1, u0elo0]
                                    · have p360_0 := h360c.1
                                      have p360_1 := h360c.2.1
                                      have p360_2 := h360c.2.2.1
                                      have p360_3 := h360c.2.2.2
                                      linarith only [hlam, p360_0]
                                  · rcases h2bigk with h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c | h398c
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h290, hc25, hlam, hphi, ht0b, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      rcases p398_3 (m.d 0 2) (by simp) with h401 | h401
                                      · rcases p398_3 (m.d 1 2) (by simp) with h402 | h402
                                        · linarith only [h0, h402, hlam]
                                        · linarith only [h288, h402, hlam]
                                      · linarith only [h401, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      rcases p398_3 (m.d 0 2) (by simp) with h406 | h406
                                      · rcases p398_3 (m.d 1 2) (by simp) with h407 | h407
                                        · linarith only [h0, h407, hlam]
                                        · linarith only [h289, h407, hlam]
                                      · linarith only [h406, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      rcases p398_3 (m.d 0 2) (by simp) with h411 | h411
                                      · rcases p398_3 (m.d 1 2) (by simp) with h412 | h412
                                        · linarith only [h0, h412, hlam]
                                        · linarith only [h290, h412, hlam]
                                      · linarith only [h411, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h301, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h301, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h4, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h288, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h301, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h303, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h5, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h289, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h305, hlam, p398_1]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h6, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h290, hlam, p398_0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h290, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [h0, h290, hc24, hlam, hphi, ht0b, ht45, ht5b, p398_1, u0elo0]
                                    · have p398_0 := h398c.1
                                      have p398_1 := h398c.2.1
                                      have p398_2 := h398c.2.2.1
                                      have p398_3 := h398c.2.2.2
                                      linarith only [hlam, p398_0]
                                  · linarith only [h359, hlam, p308_1, u0elo4]
                                  · rcases h2bigk with h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c | h437c
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, h290, hc25, hlam, hphi, ht0b, ht5b, p437_1, u0elo0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      rcases p437_3 (m.d 0 2) (by simp) with h440 | h440
                                      · rcases p437_3 (m.d 1 2) (by simp) with h441 | h441
                                        · linarith only [h0, h441, hlam]
                                        · linarith only [h288, h441, hlam]
                                      · linarith only [h440, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      rcases p437_3 (m.d 0 2) (by simp) with h445 | h445
                                      · rcases p437_3 (m.d 1 2) (by simp) with h446 | h446
                                        · linarith only [h0, h446, hlam]
                                        · linarith only [h289, h446, hlam]
                                      · linarith only [h445, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      rcases p437_3 (m.d 0 2) (by simp) with h450 | h450
                                      · rcases p437_3 (m.d 1 2) (by simp) with h451 | h451
                                        · linarith only [h0, h451, hlam]
                                        · linarith only [h290, h451, hlam]
                                      · linarith only [h450, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1, u0elo0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, h301, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1, u0elo0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, h301, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1, u0elo0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h4, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h288, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h301, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h303, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h5, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h289, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1, u0elo0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h305, hlam, p437_1]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h6, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h290, hlam, p437_0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, h290, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p437_1, u0elo0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [h0, h290, hc24, hlam, hphi, ht0b, ht45, ht5b, p437_1, u0elo0]
                                    · have p437_0 := h437c.1
                                      have p437_1 := h437c.2.1
                                      have p437_2 := h437c.2.2.1
                                      have p437_3 := h437c.2.2.2
                                      linarith only [hlam, p437_0]
                                  · rcases h2bigk with h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, h290, hc25, hlam, hphi, ht0b, ht5b, p475_1, u0elo0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      rcases p475_3 (m.d 0 2) (by simp) with h478 | h478
                                      · rcases p475_3 (m.d 1 2) (by simp) with h479 | h479
                                        · linarith only [h0, h479, hlam]
                                        · linarith only [h288, h479, hlam]
                                      · linarith only [h478, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      rcases p475_3 (m.d 0 2) (by simp) with h483 | h483
                                      · rcases p475_3 (m.d 1 2) (by simp) with h484 | h484
                                        · linarith only [h0, h484, hlam]
                                        · linarith only [h289, h484, hlam]
                                      · linarith only [h483, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      rcases p475_3 (m.d 0 2) (by simp) with h488 | h488
                                      · rcases p475_3 (m.d 1 2) (by simp) with h489 | h489
                                        · linarith only [h0, h489, hlam]
                                        · linarith only [h290, h489, hlam]
                                      · linarith only [h488, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p475_1, u0elo0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, h301, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p475_1, u0elo0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, h301, h305, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p475_1, u0elo0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h4, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h288, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h301, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h303, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h5, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h289, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p475_1, u0elo0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h305, hlam, p475_1]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h6, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h290, hlam, p475_0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, h290, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p475_1, u0elo0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [h0, h290, hc24, hlam, hphi, ht0b, ht45, ht5b, p475_1, u0elo0]
                                    · have p475_0 := h475c.1
                                      have p475_1 := h475c.2.1
                                      have p475_2 := h475c.2.2.1
                                      have p475_3 := h475c.2.2.2
                                      linarith only [hlam, p475_0]
                                · linarith only [h218, h358, hlam]
                              · linarith only [h357, h7, hlam]
                          · linarith only [h354, h4, hlam]
                        · linarith only [h1, h353, hlam]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [h287, hlam, p308_1]
                      · have p308_0 := h308c.1
                        have p308_1 := h308c.2.1
                        have p308_2 := h308c.2.2.1
                        have p308_3 := h308c.2.2.2
                        linarith only [hlam, p308_0]
                    · linarith only [h287, h307, h7, hlam]
        · linarith only [h0, h288, h290, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · linarith only [h0, h288, h289, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h522 | h522
      · linarith only [h0, h288, h4, h522, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
        · linarith only [h0, h288, h4, h524, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
          · linarith only [h1, h526, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h528 | h528
            · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
              · linarith only [h4, h529, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
                · linarith only [h218, h4, h531, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h534 | h534
                    · rcases h0bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h288, h5, h531, h533, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h288, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h2, h528, hc45, hlam, hphi, ht0b, ht5b, p535_1, u0elo0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h288, h531, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h0, hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h288, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo1]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h0, h288, h5, h531, h533, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h0, h288, h531, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h1, hlam, p535_1]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h4, hlam, p535_1]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h7, hlam, p535_1]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h218, hlam, p535_1]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h2, hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h5, hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h288, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo3]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h0, h288, h5, h531, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h3, hlam, p535_0]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h6, hlam, p535_1]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h288, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1, u0elo4]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [h287, hlam, p535_1]
                      · have p535_0 := h535c.1
                        have p535_1 := h535c.2.1
                        have p535_2 := h535c.2.2.1
                        have p535_3 := h535c.2.2.2
                        linarith only [hlam, p535_0]
                    · linarith only [h2, h528, h534, h7, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h287, h5, h522, h533, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
              · linarith only [h0, h287, h4, h528, h563, h7, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
                · linarith only [h0, h218, h5, h563, h565, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h567 | h567
                  · linarith only [h0, h288, h5, h526, h528, h567, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h287, h5, h522, h567, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
    · rcases m.htr 1 2 4 (by decide) (by decide) with h571 | h571
      · rcases m.htr 1 2 5 (by decide) (by decide) with h572 | h572
        · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
          · linarith only [h1, h573, h7, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h575 | h575
            · linarith only [h2, h287, h575, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h577 | h577
              · linarith only [h0, h570, h577, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h579 | h579
                · linarith only [h1, h218, h570, h579, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h581 | h581
                  · linarith only [h0, h287, h571, h581, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h583 | h583
                    · rcases h0bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p584_1, u0elo0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        rcases p584_3 (m.d 0 1) (by simp) with h587 | h587
                        · rcases p584_3 (m.d 0 2) (by simp) with h588 | h588
                          · linarith only [h0, h588, hlam]
                          · linarith only [h4, h588, hlam]
                        · linarith only [h1, h587, hlam]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        rcases p584_3 (m.d 0 1) (by simp) with h592 | h592
                        · rcases p584_3 (m.d 0 2) (by simp) with h593 | h593
                          · linarith only [h0, h593, hlam]
                          · linarith only [h5, h593, hlam]
                        · linarith only [h2, h592, hlam]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        rcases p584_3 (m.d 0 1) (by simp) with h597 | h597
                        · rcases p584_3 (m.d 0 2) (by simp) with h598 | h598
                          · linarith only [h0, h598, hlam]
                          · linarith only [h598, h6, hlam]
                        · linarith only [h3, h597, hlam]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h0, hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        rcases p584_3 (m.d 0 1) (by simp) with h604 | h604
                        · rcases p584_3 (m.d 0 2) (by simp) with h605 | h605
                          · rcases p584_3 (m.d 0 3) (by simp) with h606 | h606
                            · linarith only [h4, h606, hlam]
                            · rcases p584_3 (m.d 0 4) (by simp) with h608 | h608
                              · linarith only [h5, h608, hlam]
                              · linarith only [h608, h7, hlam]
                          · linarith only [h4, h605, hlam]
                        · linarith only [h1, h604, hlam]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        rcases p584_3 (m.d 0 1) (by simp) with h613 | h613
                        · rcases p584_3 (m.d 0 2) (by simp) with h614 | h614
                          · rcases p584_3 (m.d 0 3) (by simp) with h615 | h615
                            · linarith only [h4, h615, hlam]
                            · rcases p584_3 (m.d 0 4) (by simp) with h617 | h617
                              · linarith only [h5, h617, hlam]
                              · rcases p584_3 (m.d 0 5) (by simp) with h619 | h619
                                · linarith only [h6, h619, hlam]
                                · linarith only [h287, h619, hlam]
                          · linarith only [h5, h614, hlam]
                        · linarith only [h2, h613, hlam]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        rcases p584_3 (m.d 0 1) (by simp) with h624 | h624
                        · rcases p584_3 (m.d 0 2) (by simp) with h625 | h625
                          · rcases p584_3 (m.d 0 3) (by simp) with h626 | h626
                            · linarith only [h4, h626, hlam]
                            · rcases p584_3 (m.d 0 4) (by simp) with h628 | h628
                              · linarith only [h5, h628, hlam]
                              · rcases p584_3 (m.d 0 5) (by simp) with h630 | h630
                                · linarith only [h6, h630, hlam]
                                · rcases h0emin with h632 | h632 | h632 | h632 | h632
                                  · rcases h2bigk with h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c | h633c
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h572, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p633_1, u0elo1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      rcases p633_3 (m.d 0 2) (by simp) with h636 | h636
                                      · rcases p633_3 (m.d 1 2) (by simp) with h637 | h637
                                        · linarith only [h0, h637, hlam]
                                        · linarith only [h570, h637, hlam]
                                      · linarith only [h636, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      rcases p633_3 (m.d 0 2) (by simp) with h641 | h641
                                      · rcases p633_3 (m.d 1 2) (by simp) with h642 | h642
                                        · linarith only [h0, h642, hlam]
                                        · linarith only [h571, h642, hlam]
                                      · linarith only [h641, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      rcases p633_3 (m.d 0 2) (by simp) with h646 | h646
                                      · rcases p633_3 (m.d 1 2) (by simp) with h647 | h647
                                        · linarith only [h0, h647, hlam]
                                        · linarith only [h572, h647, hlam]
                                      · linarith only [h646, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, h577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h4, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h570, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h577, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h579, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h5, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h571, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h581, hlam, p633_1]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h6, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h572, hlam, p633_0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [h3, h572, hc24, hlam, hphi, ht0b, ht45, ht5b, p633_1, u0elo0]
                                    · have p633_0 := h633c.1
                                      have p633_1 := h633c.2.1
                                      have p633_2 := h633c.2.2.1
                                      have p633_3 := h633c.2.2.2
                                      linarith only [hlam, p633_0]
                                  · rcases h2bigk with h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h570, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1, u0elo0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      rcases p671_3 (m.d 0 2) (by simp) with h674 | h674
                                      · rcases p671_3 (m.d 1 2) (by simp) with h675 | h675
                                        · linarith only [h0, h675, hlam]
                                        · linarith only [h570, h675, hlam]
                                      · linarith only [h674, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      rcases p671_3 (m.d 0 2) (by simp) with h679 | h679
                                      · rcases p671_3 (m.d 1 2) (by simp) with h680 | h680
                                        · linarith only [h0, h680, hlam]
                                        · linarith only [h571, h680, hlam]
                                      · linarith only [h679, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      rcases p671_3 (m.d 0 2) (by simp) with h684 | h684
                                      · rcases p671_3 (m.d 1 2) (by simp) with h685 | h685
                                        · linarith only [h0, h685, hlam]
                                        · linarith only [h572, h685, hlam]
                                      · linarith only [h684, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1, u0elo0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1, u0elo0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1, u0elo0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h4, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h570, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h577, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h579, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h5, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h571, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1, u0elo0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h581, hlam, p671_1]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h6, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h572, hlam, p671_0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1, u0elo0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [h0, h3, h572, hc24, hlam, hphi, ht0b, ht45, ht5b, p584_1, p671_1, u0elo0]
                                    · have p671_0 := h671c.1
                                      have p671_1 := h671c.2.1
                                      have p671_2 := h671c.2.2.1
                                      have p671_3 := h671c.2.2.2
                                      linarith only [hlam, p671_0]
                                  · linarith only [h287, h583, h632, h7, hc34, hlam, ht01, ht12, ht23]
                                  · linarith only [h287, h583, h632, hc34, hlam, ht01, ht12, ht23]
                                  · linarith only [h0, h632, hlam, p584_1, u0elo0]
                          · linarith only [h6, h625, hlam]
                        · linarith only [h3, h624, hlam]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h1, hlam, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h4, hlam, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h7, hlam, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h218, hlam, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h2, hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h5, hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h287, h583, hc03, hc34, hlam, hphi, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h287, hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h3, hlam, p584_0]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h6, hlam, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h1, h287, h570, h583, hc23, hc34, hlam, hphi, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [h1, h287, h570, h583, h7, hc23, hc34, hlam, hphi, p584_1]
                      · have p584_0 := h584c.1
                        have p584_1 := h584c.2.1
                        have p584_2 := h584c.2.2.1
                        have p584_3 := h584c.2.2.2
                        linarith only [hlam, p584_0]
                    · rcases h0bigk with h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h0, h572, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p729_1, u0elo0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h732 | h732
                        · rcases p729_3 (m.d 0 2) (by simp) with h733 | h733
                          · linarith only [h0, h733, hlam]
                          · linarith only [h4, h733, hlam]
                        · linarith only [h1, h732, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h737 | h737
                        · rcases p729_3 (m.d 0 2) (by simp) with h738 | h738
                          · linarith only [h0, h738, hlam]
                          · linarith only [h5, h738, hlam]
                        · linarith only [h2, h737, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h742 | h742
                        · rcases p729_3 (m.d 0 2) (by simp) with h743 | h743
                          · linarith only [h0, h743, hlam]
                          · linarith only [h6, h743, hlam]
                        · linarith only [h3, h742, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h0, hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h749 | h749
                        · rcases p729_3 (m.d 0 2) (by simp) with h750 | h750
                          · rcases p729_3 (m.d 0 3) (by simp) with h751 | h751
                            · linarith only [h4, h751, hlam]
                            · rcases p729_3 (m.d 0 4) (by simp) with h753 | h753
                              · linarith only [h5, h753, hlam]
                              · linarith only [h7, h753, hlam]
                          · linarith only [h4, h750, hlam]
                        · linarith only [h1, h749, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h758 | h758
                        · rcases p729_3 (m.d 0 2) (by simp) with h759 | h759
                          · rcases p729_3 (m.d 0 3) (by simp) with h760 | h760
                            · linarith only [h4, h760, hlam]
                            · rcases p729_3 (m.d 0 4) (by simp) with h762 | h762
                              · linarith only [h5, h762, hlam]
                              · rcases p729_3 (m.d 0 5) (by simp) with h764 | h764
                                · linarith only [h6, h764, hlam]
                                · linarith only [h287, h764, hlam]
                          · linarith only [h5, h759, hlam]
                        · linarith only [h2, h758, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h769 | h769
                        · rcases p729_3 (m.d 0 2) (by simp) with h770 | h770
                          · rcases p729_3 (m.d 0 3) (by simp) with h771 | h771
                            · linarith only [h4, h771, hlam]
                            · rcases p729_3 (m.d 0 4) (by simp) with h773 | h773
                              · linarith only [h5, h773, hlam]
                              · rcases p729_3 (m.d 0 5) (by simp) with h775 | h775
                                · linarith only [h6, h775, hlam]
                                · rcases h0emin with h777 | h777 | h777 | h777 | h777
                                  · rcases h2bigk with h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h572, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1, u0elo0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      rcases p778_3 (m.d 0 2) (by simp) with h781 | h781
                                      · rcases p778_3 (m.d 1 2) (by simp) with h782 | h782
                                        · linarith only [h0, h782, hlam]
                                        · linarith only [h570, h782, hlam]
                                      · linarith only [h781, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      rcases p778_3 (m.d 0 2) (by simp) with h786 | h786
                                      · rcases p778_3 (m.d 1 2) (by simp) with h787 | h787
                                        · linarith only [h0, h787, hlam]
                                        · linarith only [h571, h787, hlam]
                                      · linarith only [h786, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      rcases p778_3 (m.d 0 2) (by simp) with h791 | h791
                                      · rcases p778_3 (m.d 1 2) (by simp) with h792 | h792
                                        · linarith only [h0, h792, hlam]
                                        · linarith only [h572, h792, hlam]
                                      · linarith only [h791, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1, u0elo0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1, u0elo0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1, u0elo0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h4, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h570, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h577, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h579, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h5, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h571, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1, u0elo0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h581, hlam, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h6, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h572, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1, u0elo0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h3, h572, hc24, hlam, hphi, ht0b, ht45, ht5b, p729_1, p778_1, u0elo0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                  · rcases h2bigk with h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, h570, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p816_1, u0elo0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      rcases p816_3 (m.d 0 2) (by simp) with h819 | h819
                                      · rcases p816_3 (m.d 1 2) (by simp) with h820 | h820
                                        · linarith only [h0, h820, hlam]
                                        · linarith only [h570, h820, hlam]
                                      · linarith only [h819, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      rcases p816_3 (m.d 0 2) (by simp) with h824 | h824
                                      · rcases p816_3 (m.d 1 2) (by simp) with h825 | h825
                                        · linarith only [h0, h825, hlam]
                                        · linarith only [h571, h825, hlam]
                                      · linarith only [h824, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      rcases p816_3 (m.d 0 2) (by simp) with h829 | h829
                                      · rcases p816_3 (m.d 1 2) (by simp) with h830 | h830
                                        · linarith only [h0, h830, hlam]
                                        · linarith only [h572, h830, hlam]
                                      · linarith only [h829, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p816_1, u0elo0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, h577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p816_1, u0elo0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p816_1, u0elo0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h4, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h570, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h577, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h579, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h5, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h571, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p816_1, u0elo0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h581, hlam, p816_1]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h6, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h572, hlam, p816_0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p816_1, u0elo0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [h0, h3, h572, hc24, hlam, hphi, ht0b, ht45, ht5b, p729_1, p816_1, u0elo0]
                                    · have p816_0 := h816c.1
                                      have p816_1 := h816c.2.1
                                      have p816_2 := h816c.2.2.1
                                      have p816_3 := h816c.2.2.2
                                      linarith only [hlam, p816_0]
                                  · linarith only [h583, h7, h777, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h0, h287, h777, hlam, p729_1, u0elo0]
                                  · linarith only [h0, h777, hlam, p729_1, u0elo0]
                          · linarith only [h6, h770, hlam]
                        · linarith only [h3, h769, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h1, hlam, p729_1]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h4, hlam, p729_1]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h7, hlam, p729_1]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h218, hlam, p729_1]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h2, hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h5, hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h1, h570, h583, h7, hc23, hc45, hlam, hphi, ht34, p729_1]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h287, hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h3, hlam, p729_0]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [h6, hlam, p729_1]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h871 | h871
                        · rcases p729_3 (m.d 0 2) (by simp) with h872 | h872
                          · rcases p729_3 (m.d 0 3) (by simp) with h873 | h873
                            · linarith only [h218, h873, hlam]
                            · rcases p729_3 (m.d 0 4) (by simp) with h875 | h875
                              · linarith only [h287, h875, hlam]
                              · linarith only [h7, h875, hlam]
                          · linarith only [h4, h872, hlam]
                        · linarith only [h1, h871, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        rcases p729_3 (m.d 0 1) (by simp) with h880 | h880
                        · rcases p729_3 (m.d 0 2) (by simp) with h881 | h881
                          · rcases p729_3 (m.d 0 3) (by simp) with h882 | h882
                            · linarith only [h218, h882, hlam]
                            · rcases p729_3 (m.d 0 4) (by simp) with h884 | h884
                              · linarith only [h287, h884, hlam]
                              · rcases p729_3 (m.d 0 5) (by simp) with h886 | h886
                                · rcases h0emin with h887 | h887 | h887 | h887 | h887
                                  · rcases h2bigk with h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, h572, hc25, hlam, hphi, ht0b, ht5b, p888_1, u0elo0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      rcases p888_3 (m.d 0 2) (by simp) with h891 | h891
                                      · rcases p888_3 (m.d 1 2) (by simp) with h892 | h892
                                        · linarith only [h0, h892, hlam]
                                        · linarith only [h570, h892, hlam]
                                      · linarith only [h891, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      rcases p888_3 (m.d 0 2) (by simp) with h896 | h896
                                      · rcases p888_3 (m.d 1 2) (by simp) with h897 | h897
                                        · linarith only [h0, h897, hlam]
                                        · linarith only [h571, h897, hlam]
                                      · linarith only [h896, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      rcases p888_3 (m.d 0 2) (by simp) with h901 | h901
                                      · rcases p888_3 (m.d 1 2) (by simp) with h902 | h902
                                        · linarith only [h0, h902, hlam]
                                        · linarith only [h572, h902, hlam]
                                      · linarith only [h901, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p888_1, u0elo0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, h577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p888_1, u0elo0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p888_1, u0elo0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h4, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h570, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h577, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h579, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h5, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h571, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p888_1, u0elo0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h581, hlam, p888_1]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h6, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h572, hlam, p888_0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p888_1, u0elo0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [h0, h572, hc24, hlam, hphi, ht0b, ht45, ht5b, p888_1, u0elo0]
                                    · have p888_0 := h888c.1
                                      have p888_1 := h888c.2.1
                                      have p888_2 := h888c.2.2.1
                                      have p888_3 := h888c.2.2.2
                                      linarith only [hlam, p888_0]
                                  · rcases h2bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, h572, hc25, hlam, hphi, ht0b, ht5b, p926_1, u0elo0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      rcases p926_3 (m.d 0 2) (by simp) with h929 | h929
                                      · rcases p926_3 (m.d 1 2) (by simp) with h930 | h930
                                        · linarith only [h0, h930, hlam]
                                        · linarith only [h570, h930, hlam]
                                      · linarith only [h929, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      rcases p926_3 (m.d 0 2) (by simp) with h934 | h934
                                      · rcases p926_3 (m.d 1 2) (by simp) with h935 | h935
                                        · linarith only [h0, h935, hlam]
                                        · linarith only [h571, h935, hlam]
                                      · linarith only [h934, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      rcases p926_3 (m.d 0 2) (by simp) with h939 | h939
                                      · rcases p926_3 (m.d 1 2) (by simp) with h940 | h940
                                        · linarith only [h0, h940, hlam]
                                        · linarith only [h572, h940, hlam]
                                      · linarith only [h939, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, h577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h4, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h570, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h577, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h579, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h5, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h571, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h581, hlam, p926_1]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h6, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h572, hlam, p926_0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [h0, h572, hc24, hlam, hphi, ht0b, ht45, ht5b, p926_1, u0elo0]
                                    · have p926_0 := h926c.1
                                      have p926_1 := h926c.2.1
                                      have p926_2 := h926c.2.2.1
                                      have p926_3 := h926c.2.2.2
                                      linarith only [hlam, p926_0]
                                  · linarith only [h7, h887, hlam, p729_1, u0elo4]
                                  · linarith only [h887, hlam, p729_1, u0elo4]
                                  · rcases h2bigk with h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h0, h572, hc25, hlam, hphi, ht0b, ht5b, p966_1, u0elo0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      rcases p966_3 (m.d 0 2) (by simp) with h969 | h969
                                      · rcases p966_3 (m.d 1 2) (by simp) with h970 | h970
                                        · linarith only [h0, h970, hlam]
                                        · linarith only [h570, h970, hlam]
                                      · linarith only [h969, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      rcases p966_3 (m.d 0 2) (by simp) with h974 | h974
                                      · rcases p966_3 (m.d 1 2) (by simp) with h975 | h975
                                        · linarith only [h0, h975, hlam]
                                        · linarith only [h571, h975, hlam]
                                      · linarith only [h974, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      rcases p966_3 (m.d 0 2) (by simp) with h979 | h979
                                      · rcases p966_3 (m.d 1 2) (by simp) with h980 | h980
                                        · linarith only [h0, h980, hlam]
                                        · linarith only [h572, h980, hlam]
                                      · linarith only [h979, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h0, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h0, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p966_1, u0elo0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h0, h577, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p966_1, u0elo0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h0, h577, h581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p966_1, u0elo0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h4, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h570, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h577, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h579, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h5, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h571, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p966_1, u0elo1]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h581, hlam, p966_1]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h6, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h572, hlam, p966_0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h0, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p966_1, u0elo0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [h0, h572, hc24, hlam, hphi, ht0b, ht45, ht5b, p966_1, u0elo0]
                                    · have p966_0 := h966c.1
                                      have p966_1 := h966c.2.1
                                      have p966_2 := h966c.2.2.1
                                      have p966_3 := h966c.2.2.2
                                      linarith only [hlam, p966_0]
                                · linarith only [h287, h886, hlam]
                          · linarith only [h5, h881, hlam]
                        · linarith only [h2, h880, hlam]
                      · have p729_0 := h729c.1
                        have p729_1 := h729c.2.1
                        have p729_2 := h729c.2.2.1
                        have p729_3 := h729c.2.2.2
                        linarith only [hlam, p729_0]
        · linarith only [h0, h570, h572, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · linarith only [h0, h5, h570, h571, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1010 | h1010
      · linarith only [h0, h1010, h4, h570, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1012 | h1012
        · linarith only [h0, h1012, h4, h570, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1014 | h1014
          · linarith only [h1, h1014, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1016 | h1016
            · linarith only [h1016, h2, h287, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1018 | h1018
              · linarith only [h1018, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1020 | h1020
                · linarith only [h1020, h218, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1022 | h1022
                  · linarith only [h0, h1022, h287, h4, h5, h570, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1024 | h1024
                    · linarith only [h1024, h287, h4, h570, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1024, h4, h570, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h218
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h218

end R2N4
