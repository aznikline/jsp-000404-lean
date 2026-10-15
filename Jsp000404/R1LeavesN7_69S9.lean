import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_69S8

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h268 | h268
  · rcases m.htr 0 2 3 (by decide) (by decide) with h269 | h269
    · rcases m.htr 0 2 4 (by decide) (by decide) with h270 | h270
      · rcases m.htr 0 2 5 (by decide) (by decide) with h271 | h271
        · rcases m.htr 0 3 4 (by decide) (by decide) with h272 | h272
          · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
            · rcases m.htr 1 2 3 (by decide) (by decide) with h274 | h274
              · rcases m.htr 1 2 4 (by decide) (by decide) with h275 | h275
                · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                    · linarith only [h268, h277, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h268, h272, h277, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h271, h276, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h268, h270, h274, h275, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h269, h274, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h272, h273, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h284 | h284
            · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
              · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
                · rcases m.htr 1 2 5 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                    · linarith only [h268, h272, h288, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h290 | h290
                      · linarith only [h0, h268, h290, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h284, h290, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h271, h287, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h268, h270, h285, h286, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h269, h285, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
              · rcases m.htr 1 2 4 (by decide) (by decide) with h297 | h297
                · rcases m.htr 1 2 5 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h299 | h299
                    · linarith only [h268, h272, h299, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h301 | h301
                      · linarith only [h0, h268, h301, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                        · linarith only [h269, h272, h303, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h268, h284, h296, h305, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h307 | h307
                            · linarith only [h270, h307, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h309 | h309
                              · rcases h2bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h0, hlam, p310_1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1, u0elo1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p310_1, u0elo1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p310_1, u0elo1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  rcases p310_3 (m.d 0 2) (by simp) with h316 | h316
                                  · linarith only [h0, h316, hlam]
                                  · rcases p310_3 (m.d 1 2) (by simp) with h318 | h318
                                    · rcases p310_3 (m.d 2 3) (by simp) with h319 | h319
                                      · linarith only [h296, h319, hlam]
                                      · rcases p310_3 (m.d 2 4) (by simp) with h321 | h321
                                        · linarith only [h297, h321, hlam]
                                        · rcases p310_3 (m.d 2 5) (by simp) with h323 | h323
                                          · linarith only [h298, h323, hlam]
                                          · rcases h3bigk with h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h296, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p325_1, u0elo2]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h284, hc23, hlam, hphi, ht34, ht45, p325_1, u5elo3]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h272, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h284, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h268, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h0, h268, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p310_1, p325_1]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h299, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h301, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h269, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h296, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h303, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h305, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              rcases p325_3 (m.d 0 3) (by simp) with h341 | h341
                                              · linarith only [h341, hlam, p325_0]
                                              · rcases p325_3 (m.d 1 3) (by simp) with h343 | h343
                                                · linarith only [h299, h343, hlam]
                                                · rcases p325_3 (m.d 2 3) (by simp) with h345 | h345
                                                  · linarith only [h303, h345, hlam]
                                                  · rcases p325_3 (m.d 3 4) (by simp) with h347 | h347
                                                    · rcases p325_3 (m.d 3 5) (by simp) with h348 | h348
                                                      · linarith only [h309, h348, hlam]
                                                      · linarith only [h284, h348, hlam]
                                                    · linarith only [h347, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              rcases p325_3 (m.d 0 3) (by simp) with h352 | h352
                                              · linarith only [h272, h352, hlam]
                                              · linarith only [h268, h352, hlam]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              rcases p325_3 (m.d 0 3) (by simp) with h355 | h355
                                              · linarith only [h272, h355, hlam]
                                              · linarith only [h269, h355, hlam]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h268, h284, h296, hc23, hc34, hlam, hphi, p325_1]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h268, h296, hc23, hlam, hphi, ht34, ht45, p325_1, u5elo3]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h296, hc23, hlam, hphi, ht34, ht45, p325_1, u5elo3]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [hc23, hlam, hphi, ht34, ht45, p325_1, u5elo3]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [h309, hlam, p325_0]
                                            · have p325_0 := h325c.1
                                              have p325_1 := h325c.2.1
                                              have p325_2 := h325c.2.2.1
                                              have p325_3 := h325c.2.2.2
                                              linarith only [hlam, p325_0]
                                    · linarith only [h0, h318, hlam]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  rcases p310_3 (m.d 0 2) (by simp) with h367 | h367
                                  · linarith only [h0, h367, hlam]
                                  · linarith only [h269, h367, hlam]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  rcases p310_3 (m.d 0 2) (by simp) with h370 | h370
                                  · linarith only [h0, h370, hlam]
                                  · linarith only [h270, h370, hlam]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  rcases p310_3 (m.d 0 2) (by simp) with h373 | h373
                                  · linarith only [h0, h373, hlam]
                                  · linarith only [h271, h373, hlam]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h269, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h296, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h303, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h305, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h270, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h297, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h307, hc23, hc45, hlam, hphi, ht34, p310_1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h307, hlam, p310_1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h271, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h298, hlam, p310_0]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h271, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p310_1, u0elo1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [h271, hc24, hlam, hphi, ht0b, ht45, ht5b, p310_1, u0elo1]
                                · have p310_0 := h310c.1
                                  have p310_1 := h310c.2.1
                                  have p310_2 := h310c.2.2.1
                                  have p310_3 := h310c.2.2.2
                                  linarith only [hlam, p310_0]
                              · linarith only [h268, h272, h296, h309, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h271, h298, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h268, h270, h296, h297, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h269, h296, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h269, h271, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h396 | h396
        · rcases m.htr 0 3 4 (by decide) (by decide) with h397 | h397
          · linarith only [h0, h268, h270, h397, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h399 | h399
            · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
              · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
                · rcases m.htr 1 2 5 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
                    · linarith only [h0, h268, h270, h397, h401, h403, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h405 | h405
                      · linarith only [h0, h268, h270, h401, h405, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h399, h405, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h270, h396, h401, h402, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                    · linarith only [h268, h397, h399, h410, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h412 | h412
                      · linarith only [h0, h268, h270, h412, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                      · linarith only [h399, h412, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h409, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h268, h269, h270, h400, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
              · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
                · rcases m.htr 1 2 5 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h420 | h420
                    · linarith only [h0, h268, h270, h420, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h422 | h422
                      · linarith only [h0, h268, h270, h399, h422, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                        · linarith only [h0, h268, h270, h417, h418, h420, h424, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h426 | h426
                          · linarith only [h268, h399, h417, h426, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h428 | h428
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h429 | h429
                              · rcases h2bigk with h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, hlam, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h270, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p430_1, u0elo3]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h270, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h270, hc25, hlam, hphi, ht0b, ht5b, p430_1, u0elo3]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 2) (by simp) with h436 | h436
                                  · linarith only [h0, h436, hlam]
                                  · rcases p430_3 (m.d 1 2) (by simp) with h438 | h438
                                    · rcases p430_3 (m.d 2 3) (by simp) with h439 | h439
                                      · linarith only [h417, h439, hlam]
                                      · rcases p430_3 (m.d 2 4) (by simp) with h441 | h441
                                        · linarith only [h418, h441, hlam]
                                        · linarith only [h270, h441, hlam]
                                    · linarith only [h0, h438, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h269, h270, h418, hlam, p430_2]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h270, hc01, hc12, hlam, hphi, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h270, h396, h418, hlam, p430_2]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h269, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h417, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h424, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h426, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h0, h268, h417, h418, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p430_1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h418, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 2) (by simp) with h456 | h456
                                  · linarith only [h270, h456, hlam]
                                  · linarith only [h269, h456, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  rcases p430_3 (m.d 0 2) (by simp) with h460 | h460
                                  · linarith only [h270, h460, hlam]
                                  · linarith only [h396, h460, hlam]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h396, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h419, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h396, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p430_1, u0elo1]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [h428, hlam, p430_0]
                                · have p430_0 := h430c.1
                                  have p430_1 := h430c.2.1
                                  have p430_2 := h430c.2.2.1
                                  have p430_3 := h430c.2.2.2
                                  linarith only [hlam, p430_0]
                              · linarith only [h270, h418, h420, h429, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h0, h268, h270, h417, h428, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h268, h417, h419, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h471 | h471
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                    · linarith only [h268, h472, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
                      · linarith only [h268, h399, h474, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h476 | h476
                        · linarith only [h0, h268, h417, h418, h472, h476, hlam]
                        · linarith only [h0, h268, h417, h418, h476, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h268, h396, h417, h471, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h268, h269, h270, h417, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
        · linarith only [h269, h396, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · linarith only [h0, h268, h269, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h483 | h483
    · rcases m.htr 0 2 4 (by decide) (by decide) with h484 | h484
      · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
        · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
          · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
            · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
              · rcases m.htr 1 2 4 (by decide) (by decide) with h489 | h489
                · rcases m.htr 1 2 5 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
                        · linarith only [h483, h493, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h483, h486, h493, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h268, h483, h487, h492, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h268, h486, h491, hlam]
                  · linarith only [h0, h485, h490, hlam]
                · linarith only [h0, h484, h489, hlam]
              · linarith only [h0, h483, h488, hlam]
            · linarith only [h486, h487, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
            · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
              · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                · rcases m.htr 1 2 5 (by decide) (by decide) with h505 | h505
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h507 | h507
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h508 | h508
                        · linarith only [h483, h486, h502, h508, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h510 | h510
                          · linarith only [h484, h508, h510, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h502, h510, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h486, h502, h506, h507, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h514 | h514
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
                        · linarith only [h268, h506, h515, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h517 | h517
                          · linarith only [h484, h515, h517, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h502, h517, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h268, h502, h514, hlam]
                  · linarith only [h485, h505, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h484, h504, hlam]
              · linarith only [h0, h483, h503, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h524 | h524
              · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
                · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h528 | h528
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                        · linarith only [h483, h486, h529, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h531 | h531
                          · linarith only [h483, h502, h531, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h533 | h533
                            · linarith only [h484, h533, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h535 | h535
                              · rcases h2bigk with h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h0, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h529, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p536_1, u0elo1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 2) (by simp) with h542 | h542
                                  · linarith only [h0, h542, hlam]
                                  · rcases p536_3 (m.d 1 2) (by simp) with h544 | h544
                                    · rcases p536_3 (m.d 2 3) (by simp) with h545 | h545
                                      · linarith only [h524, h545, hlam]
                                      · rcases p536_3 (m.d 2 4) (by simp) with h547 | h547
                                        · linarith only [h525, h547, hlam]
                                        · rcases p536_3 (m.d 2 5) (by simp) with h549 | h549
                                          · linarith only [h526, h549, hlam]
                                          · rcases h3bigk with h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h268, hlam, p551_1]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p551_1, u0elo2]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h486, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h502, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              rcases p551_3 (m.d 0 3) (by simp) with h557 | h557
                                              · linarith only [h268, h557, hlam]
                                              · rcases p551_3 (m.d 1 3) (by simp) with h559 | h559
                                                · rcases p551_3 (m.d 2 3) (by simp) with h560 | h560
                                                  · linarith only [h524, h560, hlam]
                                                  · rcases p551_3 (m.d 3 4) (by simp) with h562 | h562
                                                    · linarith only [h527, h562, hlam]
                                                    · linarith only [h486, h562, hlam]
                                                · linarith only [h268, h559, hlam]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h527, h529, h533, h535, hlam, p551_2]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h524, h529, h533, h535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p551_1]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h268, h502, h524, hc01, hc12, hlam, hphi, p551_1]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h483, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h524, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h529, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h531, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h268, h524, h527, hc01, hc12, hlam, hphi, p551_1]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h527, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              rcases p551_3 (m.d 0 3) (by simp) with h577 | h577
                                              · linarith only [h486, h577, hlam]
                                              · linarith only [h483, h577, hlam]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h268, h502, h524, h527, hc01, hc12, hlam, hphi, p551_1]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h268, h528, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p551_1, u5elo1]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h528, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h528, hc23, hlam, hphi, ht34, ht45, p551_1, u5elo1]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [h535, hlam, p551_0]
                                            · have p551_0 := h551c.1
                                              have p551_1 := h551c.2.1
                                              have p551_2 := h551c.2.2.1
                                              have p551_3 := h551c.2.2.2
                                              linarith only [hlam, p551_0]
                                    · linarith only [h0, h544, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h524, h527, h529, h533, h535, hlam, p536_2]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h524, h527, h533, h535, hlam, p536_2]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  rcases p536_3 (m.d 0 2) (by simp) with h591 | h591
                                  · linarith only [h0, h591, hlam]
                                  · linarith only [h485, h591, hlam]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h483, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h524, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h529, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h531, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h484, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h525, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h524, h527, h533, h535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h533, hlam, p536_1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h485, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h526, hlam, p536_0]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h485, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p536_1, u0elo1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [h485, hc24, hlam, hphi, ht0b, ht45, ht5b, p536_1, u0elo1]
                                · have p536_0 := h536c.1
                                  have p536_1 := h536c.2.1
                                  have p536_2 := h536c.2.2.1
                                  have p536_3 := h536c.2.2.2
                                  linarith only [hlam, p536_0]
                              · linarith only [h268, h486, h535, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h268, h528, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
                      · linarith only [h268, h502, h527, h611, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h268, h611, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h485, h526, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h484, h525, hlam]
              · linarith only [h0, h483, h524, hlam]
        · linarith only [h484, h485, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h618 | h618
        · rcases m.htr 0 3 4 (by decide) (by decide) with h619 | h619
          · linarith only [h483, h484, h619, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h621 | h621
            · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
              · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
                · rcases m.htr 1 2 5 (by decide) (by decide) with h624 | h624
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
                        · linarith only [h483, h619, h627, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h629 | h629
                          · linarith only [h483, h484, h622, h625, h627, h629, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h621, h629, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h619, h621, h625, h626, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h633 | h633
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                        · linarith only [h268, h625, h634, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
                          · linarith only [h483, h484, h636, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h483, h484, h621, h636, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h268, h483, h484, h621, h623, h633, hc01, hc12, hlam, hphi]
                  · linarith only [h484, h623, h624, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h641 | h641
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h642 | h642
                    · linarith only [h619, h621, h622, h623, h642, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h644 | h644
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h645 | h645
                        · linarith only [h268, h642, h645, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h647 | h647
                          · linarith only [h483, h484, h647, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h621, h647, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h268, h621, h644, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h484, h618, h641, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h483, h622, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h653 | h653
              · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
                · rcases m.htr 1 2 5 (by decide) (by decide) with h655 | h655
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h656 | h656
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h657 | h657
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h658 | h658
                        · linarith only [h268, h483, h484, h619, h654, h658, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h660 | h660
                          · linarith only [h268, h483, h484, h621, h653, h656, h658, h660, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h662 | h662
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h663 | h663
                              · rcases h2bigk with h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h0, hlam, p664_1]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h268, h484, h621, h653, h656, h657, h658, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p664_1, u5elo1]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h484, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h268, h484, h621, h653, h656, h657, h658, hc01, hc12, hc25, hlam, hphi, p664_1, u5elo1]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  rcases p664_3 (m.d 0 2) (by simp) with h670 | h670
                                  · linarith only [h0, h670, hlam]
                                  · rcases p664_3 (m.d 1 2) (by simp) with h672 | h672
                                    · rcases p664_3 (m.d 2 3) (by simp) with h673 | h673
                                      · linarith only [h653, h673, hlam]
                                      · rcases p664_3 (m.d 2 4) (by simp) with h675 | h675
                                        · linarith only [h654, h675, hlam]
                                        · linarith only [h484, h675, hlam]
                                    · linarith only [h0, h672, hlam]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h483, h484, h653, h656, h658, hlam, p664_2]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h268, h484, h618, h621, h657, h660, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p664_1, u5elo1]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h484, h618, h654, hlam, p664_2]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h483, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h653, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h658, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h660, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h268, h618, h621, h654, h657, hc01, hc12, hc25, hlam, hphi, p664_1, u5elo1]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h654, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  rcases p664_3 (m.d 0 2) (by simp) with h690 | h690
                                  · linarith only [h484, h690, hlam]
                                  · linarith only [h483, h690, hlam]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  rcases p664_3 (m.d 0 2) (by simp) with h694 | h694
                                  · linarith only [h484, h694, hlam]
                                  · linarith only [h618, h694, hlam]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h618, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h655, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h618, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p664_1, u0elo1]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [h662, hlam, p664_0]
                                · have p664_0 := h664c.1
                                  have p664_1 := h664c.2.1
                                  have p664_2 := h664c.2.2.1
                                  have p664_3 := h664c.2.2.2
                                  linarith only [hlam, p664_0]
                              · linarith only [h484, h658, h663, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h484, h618, h660, h662, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h268, h657, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h705 | h705
                      · linarith only [h621, h656, h705, hc03, hc34, hlam, hphi]
                      · linarith only [h268, h705, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h618, h655, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h709 | h709
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
                    · linarith only [h268, h619, h653, h654, h710, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h712 | h712
                      · linarith only [h268, h621, h653, h654, h712, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h268, h712, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h268, h618, h653, h709, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h483, h653, hlam]
        · linarith only [h483, h618, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h718 | h718
      · rcases m.htr 0 2 5 (by decide) (by decide) with h719 | h719
        · rcases m.htr 0 3 4 (by decide) (by decide) with h720 | h720
          · rcases m.htr 0 3 5 (by decide) (by decide) with h721 | h721
            · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
              · rcases m.htr 1 2 4 (by decide) (by decide) with h723 | h723
                · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h726 | h726
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h727 | h727
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h728 | h728
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h729 | h729
                            · linarith only [h718, h729, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h731 | h731
                              · linarith only [h727, h729, h731, hlam]
                              · rcases h2bigk with h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h0, hlam, p733_1]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h483, hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h483, hc24, hlam, hphi, ht0b, ht45, ht5b, p733_1, u0elo2]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h483, hc25, hlam, hphi, ht0b, ht5b, p733_1, u0elo2]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  rcases p733_3 (m.d 0 2) (by simp) with h739 | h739
                                  · linarith only [h0, h739, hlam]
                                  · rcases p733_3 (m.d 1 2) (by simp) with h741 | h741
                                    · rcases p733_3 (m.d 2 3) (by simp) with h742 | h742
                                      · linarith only [h722, h742, hlam]
                                      · linarith only [h483, h742, hlam]
                                    · linarith only [h0, h741, hlam]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h0, h483, hc01, hc12, hlam, hphi, p733_1]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h483, h719, h722, h729, hlam, p733_2]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h483, h719, h722, hlam, p733_2]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h719, h722, h727, h729, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p733_1]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h722, hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  rcases p733_3 (m.d 0 2) (by simp) with h753 | h753
                                  · linarith only [h483, h753, hlam]
                                  · linarith only [h718, h753, hlam]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  rcases p733_3 (m.d 0 2) (by simp) with h756 | h756
                                  · linarith only [h483, h756, hlam]
                                  · linarith only [h719, h756, hlam]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h718, hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h723, hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h727, hlam, p733_1]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h729, hlam, p733_1]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h719, hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h724, hlam, p733_0]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h728, hlam, p733_1]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [h719, h727, hc34, hlam, hphi, ht0b, ht45, ht5b, p733_1, u0elo1]
                                · have p733_0 := h733c.1
                                  have p733_1 := h733c.2.1
                                  have p733_2 := h733c.2.2.1
                                  have p733_3 := h733c.2.2.2
                                  linarith only [hlam, p733_0]
                          · linarith only [h483, h728, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h483, h718, h720, h727, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h483, h718, h721, h722, h726, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h483, h718, h720, h722, h725, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h724, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h483, h718, h722, h723, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h775 | h775
                · rcases m.htr 1 2 5 (by decide) (by decide) with h776 | h776
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h777 | h777
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h778 | h778
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h779 | h779
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h780 | h780
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h781 | h781
                            · linarith only [h718, h781, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h783 | h783
                              · linarith only [h720, h781, h783, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · rcases h2bigk with h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h0, hlam, p785_1]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h483, hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h483, h779, hc34, hlam, hphi, ht0b, ht45, ht5b, p785_1, u0elo2]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h483, hc25, hlam, hphi, ht0b, ht5b, p785_1, u0elo2]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h722, hc02, hc23, hlam, hphi, p785_1]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h722, hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  rcases p785_3 (m.d 0 2) (by simp) with h794 | h794
                                  · linarith only [h0, h794, hlam]
                                  · linarith only [h718, h794, hlam]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  rcases p785_3 (m.d 0 2) (by simp) with h797 | h797
                                  · linarith only [h0, h797, hlam]
                                  · linarith only [h719, h797, hlam]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  rcases p785_3 (m.d 0 2) (by simp) with h800 | h800
                                  · linarith only [h800, hlam, p785_0]
                                  · rcases p785_3 (m.d 1 2) (by simp) with h802 | h802
                                    · linarith only [h722, h802, hlam]
                                    · linarith only [h0, h802, hlam]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p785_1]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  rcases p785_3 (m.d 0 2) (by simp) with h807 | h807
                                  · linarith only [h483, h807, hlam]
                                  · linarith only [h718, h807, hlam]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  rcases p785_3 (m.d 0 2) (by simp) with h810 | h810
                                  · linarith only [h483, h810, hlam]
                                  · linarith only [h719, h810, hlam]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h718, hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h775, hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h779, hlam, p785_1]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h781, hlam, p785_1]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h719, hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h776, hlam, p785_0]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h780, hlam, p785_1]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [h719, h779, hc34, hlam, hphi, ht0b, ht45, ht5b, p785_1, u0elo1]
                                · have p785_0 := h785c.1
                                  have p785_1 := h785c.2.1
                                  have p785_2 := h785c.2.2.1
                                  have p785_3 := h785c.2.2.2
                                  linarith only [hlam, p785_0]
                          · linarith only [h483, h780, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h722, h779, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h721, h722, h778, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h268, h720, h777, hlam]
                  · linarith only [h0, h776, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h718, h775, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h483, h718, h721, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h483, h718, h720, hlam]
        · linarith only [h718, h719, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h832 | h832
        · rcases m.htr 0 3 4 (by decide) (by decide) with h833 | h833
          · rcases m.htr 0 3 5 (by decide) (by decide) with h834 | h834
            · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
              · rcases m.htr 1 2 4 (by decide) (by decide) with h836 | h836
                · rcases m.htr 1 2 5 (by decide) (by decide) with h837 | h837
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h839 | h839
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h840 | h840
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h841 | h841
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h842 | h842
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                              · linarith only [h833, h843, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h832, h842, h843, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h0, h718, h842, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h718, h832, h840, h841, hc25, hlam, hphi, u5elo3]
                        · linarith only [h833, h840, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h718, h832, h834, h836, h838, h839, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h833, h838, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h483, h832, h835, h837, hlam]
                · linarith only [h483, h832, h835, h836, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h853 | h853
                · linarith only [h718, h832, h835, h853, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h856 | h856
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h857 | h857
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h858 | h858
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h859 | h859
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h860 | h860
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h861 | h861
                              · linarith only [h833, h861, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h832, h860, h861, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h853, h860, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h483, h859, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h835, h858, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h834, h853, h856, h857, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h268, h833, h856, hlam]
                  · linarith only [h0, h832, h855, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h718, h832, h833, h834, hc25, hlam, hphi, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h871 | h871
            · rcases m.htr 1 2 3 (by decide) (by decide) with h872 | h872
              · rcases m.htr 1 2 4 (by decide) (by decide) with h873 | h873
                · rcases m.htr 1 2 5 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h875 | h875
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h876 | h876
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h877 | h877
                        · linarith only [h483, h832, h833, h872, h877, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h483, h832, h875, h877, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h871, h876, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h881 | h881
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h882 | h882
                        · linarith only [h872, h875, h882, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h884 | h884
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h885 | h885
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h886 | h886
                              · rcases h2bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h0, hlam, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h483, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h718, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h483, h872, h875, h884, h886, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  rcases p887_3 (m.d 0 2) (by simp) with h893 | h893
                                  · linarith only [h0, h893, hlam]
                                  · rcases p887_3 (m.d 1 2) (by simp) with h895 | h895
                                    · rcases p887_3 (m.d 2 3) (by simp) with h896 | h896
                                      · linarith only [h872, h896, hlam]
                                      · linarith only [h483, h896, hlam]
                                    · linarith only [h0, h895, hlam]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h0, h483, hc01, hc12, hlam, hphi, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h483, h832, h882, h884, h886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h483, h832, h872, hlam, p887_2]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h832, h872, h884, h886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h872, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h882, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  rcases p887_3 (m.d 0 2) (by simp) with h908 | h908
                                  · linarith only [h483, h908, hlam]
                                  · linarith only [h832, h908, hlam]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h832, h873, h884, h886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h873, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h483, h832, h873, h884, h886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  rcases p887_3 (m.d 0 2) (by simp) with h915 | h915
                                  · linarith only [h718, h915, hlam]
                                  · linarith only [h832, h915, hlam]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h832, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h874, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h884, hlam, p887_1]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [h885, hlam, p887_0]
                                · have p887_0 := h887c.1
                                  have p887_1 := h887c.2.1
                                  have p887_2 := h887c.2.2.1
                                  have p887_3 := h887c.2.2.2
                                  linarith only [hlam, p887_0]
                              · linarith only [h875, h886, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h718, h885, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h483, h832, h884, hc25, hlam, hphi, u5elo3]
                      · linarith only [h483, h832, h871, h872, h881, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h832, h874, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h483, h872, h873, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h929 | h929
                · linarith only [h718, h832, h872, h929, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h933 | h933
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h934 | h934
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h935 | h935
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h936 | h936
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h937 | h937
                              · rcases h2bigk with h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c | h938c
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h0, hlam, p938_1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h483, hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h718, hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h935, h937, hc45, hlam, hphi, ht0b, ht5b, p938_1, u0elo1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h929, h934, hc02, hc23, hlam, hphi, p938_1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h872, hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h929, hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  rcases p938_3 (m.d 0 2) (by simp) with h948 | h948
                                  · linarith only [h0, h948, hlam]
                                  · linarith only [h832, h948, hlam]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  rcases p938_3 (m.d 0 2) (by simp) with h951 | h951
                                  · linarith only [h951, hlam, p938_0]
                                  · rcases p938_3 (m.d 1 2) (by simp) with h953 | h953
                                    · linarith only [h872, h953, hlam]
                                    · linarith only [h0, h953, hlam]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p938_1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h718, h832, h935, h937, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p938_1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h483, h832, h833, h872, h932, hlam, p938_2]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  rcases p938_3 (m.d 0 2) (by simp) with h960 | h960
                                  · linarith only [h960, hlam, p938_0]
                                  · rcases p938_3 (m.d 1 2) (by simp) with h962 | h962
                                    · linarith only [h929, h962, hlam]
                                    · linarith only [h0, h962, hlam]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p938_1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h934, hlam, p938_1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  rcases p938_3 (m.d 0 2) (by simp) with h968 | h968
                                  · linarith only [h718, h968, hlam]
                                  · linarith only [h832, h968, hlam]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h832, hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h931, hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h935, hlam, p938_1]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [h936, hlam, p938_0]
                                · have p938_0 := h938c.1
                                  have p938_1 := h938c.2.1
                                  have p938_2 := h938c.2.2.1
                                  have p938_3 := h938c.2.2.2
                                  linarith only [hlam, p938_0]
                              · linarith only [h483, h833, h937, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h718, h832, h935, h936, hc35, hlam, hphi, u5elo4]
                          · linarith only [h483, h832, h833, h872, h932, h935, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h872, h932, h934, hlam]
                      · linarith only [h833, h871, h932, h933, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h981 | h981
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h982 | h982
                        · linarith only [h268, h932, h982, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h872, h982, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h871, h872, h981, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h832, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h483, h832, h871, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h988 | h988
          · rcases m.htr 0 3 5 (by decide) (by decide) with h989 | h989
            · rcases m.htr 1 2 3 (by decide) (by decide) with h990 | h990
              · rcases m.htr 1 2 4 (by decide) (by decide) with h991 | h991
                · rcases m.htr 1 2 5 (by decide) (by decide) with h992 | h992
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h994 | h994
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h995 | h995
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h996 | h996
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h997 | h997
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h998 | h998
                              · linarith only [h988, h998, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · rcases h2bigk with h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c | h1000c
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, hlam, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h483, hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h718, hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h832, hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  rcases p1000_3 (m.d 0 2) (by simp) with h1006 | h1006
                                  · linarith only [h0, h1006, hlam]
                                  · rcases p1000_3 (m.d 1 2) (by simp) with h1008 | h1008
                                    · rcases p1000_3 (m.d 2 3) (by simp) with h1009 | h1009
                                      · linarith only [h1009, h990, hlam]
                                      · linarith only [h1009, h483, hlam]
                                    · linarith only [h0, h1008, hlam]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h995, h997, h998, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h997, h998, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, h832, hc01, hc12, hlam, hphi, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, h990, hc01, hc12, hlam, hphi, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h990, hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, h832, h990, h992, h997, h998, hc01, hc13, hc34, hlam, hphi, ht45, p1000_1, u5elo1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, h832, h990, hc01, hc12, hlam, hphi, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, h991, hc01, hc12, hlam, hphi, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h991, hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h995, hlam, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, h832, h990, h995, hc01, hc12, hlam, hphi, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h0, h992, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1000_1, u5elo1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h992, hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h996, hlam, p1000_1]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [h997, hlam, p1000_0]
                                · have p1000_0 := h1000c.1
                                  have p1000_1 := h1000c.2.1
                                  have p1000_2 := h1000c.2.2.1
                                  have p1000_3 := h1000c.2.2.2
                                  linarith only [hlam, p1000_0]
                            · linarith only [h0, h718, h997, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h989, h996, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h483, h988, h995, hlam]
                      · linarith only [h989, h994, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h483, h988, h989, h990, h993, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h0, h992, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h483, h990, h991, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1039 | h1039
                · linarith only [h0, h1039, h718, h990, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1041 | h1041
                  · linarith only [h0, h1041, h832, h990, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h1041, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h988, h989, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1045 | h1045
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1046 | h1046
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1047 | h1047
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1048 | h1048
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1049 | h1049
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1050 | h1050
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1051 | h1051
                        · linarith only [h1045, h1046, h1051, h988, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h1049, h1051, h483, hc01, hc13, hlam, hphi]
                      · linarith only [h1045, h1050, h988, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1055 | h1055
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1056 | h1056
                        · linarith only [h1046, h1049, h1056, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1058 | h1058
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1059 | h1059
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1060 | h1060
                              · rcases h2bigk with h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, hlam, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h483, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h718, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h832, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  rcases p1061_3 (m.d 0 2) (by simp) with h1067 | h1067
                                  · linarith only [h0, h1067, hlam]
                                  · rcases p1061_3 (m.d 1 2) (by simp) with h1069 | h1069
                                    · rcases p1061_3 (m.d 2 3) (by simp) with h1070 | h1070
                                      · linarith only [h1046, h1070, hlam]
                                      · linarith only [h1070, h483, hlam]
                                    · linarith only [h0, h1069, hlam]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h483, hc01, hc12, hlam, hphi, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h718, hc01, hc12, hlam, hphi, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h832, hc01, hc12, hlam, hphi, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h1046, h1049, hc01, hc34, hlam, hphi, ht12, ht23, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h1046, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h1056, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h1046, h1049, h832, hc01, hc34, hlam, hphi, ht12, ht23, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h1047, hc01, hc12, hlam, hphi, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h1047, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h1047, h483, hc01, hc12, hlam, hphi, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h1047, h832, hc01, hc12, hlam, hphi, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h0, h1048, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1061_1, u5elo1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h1048, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h1058, hlam, p1061_1]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [h1059, hlam, p1061_0]
                                · have p1061_0 := h1061c.1
                                  have p1061_1 := h1061c.2.1
                                  have p1061_2 := h1061c.2.2.1
                                  have p1061_3 := h1061c.2.2.2
                                  linarith only [hlam, p1061_0]
                              · linarith only [h1049, h1060, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h0, h1059, h718, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1045, h1058, h988, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h1045, h1046, h1055, h483, hlam]
                  · linarith only [h0, h1048, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h1046, h1047, h483, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
                · linarith only [h0, h1046, h1099, h718, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1101 | h1101
                  · linarith only [h0, h1046, h1101, h832, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h1101, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1104 | h1104
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1105 | h1105
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1106 | h1106
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1107 | h1107
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1108 | h1108
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                        · linarith only [h0, h1104, h1109, h483, h988, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h1107, h1109, h483, hc01, hc13, hlam, hphi]
                      · linarith only [h1107, h1108, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1113 | h1113
                      · linarith only [h0, h1045, h1107, h1113, h483, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1113, h268, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1105, h1106, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h1104, h1105, h483, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1118 | h1118
                · linarith only [h0, h1104, h1118, h718, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1120 | h1120
                  · linarith only [h0, h1104, h1120, h832, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h1120, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_0_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_0_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
