import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6287 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 2 5 (by decide) (by decide) with h6288 | h6288
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6289 | h6289
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6290 | h6290
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6291 | h6291
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6292 | h6292
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6293 | h6293
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6294 | h6294
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6295 | h6295
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6296 | h6296
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6297 | h6297
                    · linarith only [h4553, h6287, h6291, h6297, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h4553, h6287, h6290, h6291, h6297, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h4553, h6289, h6296, hlam]
                · linarith only [h4553, h6287, h6295, hlam]
              · linarith only [h4553, h6287, h6290, h6291, h6294, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h4553, h6288, h6291, h6293, hlam]
          · linarith only [h4553, h6287, h6291, h6292, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6305 | h6305
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6306 | h6306
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6307 | h6307
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6308 | h6308
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6309 | h6309
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6310 | h6310
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6311 | h6311
                      · rcases h2bigk with h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c | h6312c
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h0, hlam, p6312_1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h4553, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6308, h6311, hc45, hlam, hphi, ht0b, ht5b, p6312_1, u0elo1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          rcases p6312_3 (m.d 0 2) (by simp) with h6317 | h6317
                          · rcases p6312_3 (m.d 1 2) (by simp) with h6318 | h6318
                            · rcases p6312_3 (m.d 2 3) (by simp) with h6319 | h6319
                              · rcases p6312_3 (m.d 2 4) (by simp) with h6320 | h6320
                                · linarith only [h6287, h6320, hlam]
                                · linarith only [h6310, h6320, hlam]
                              · linarith only [h6309, h6319, hlam]
                            · linarith only [h6306, h6318, hlam]
                          · linarith only [h6317, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6291, hc02, hc23, hlam, hphi, p6312_1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6291, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6291, h6308, h6311, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6312_1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          rcases p6312_3 (m.d 0 2) (by simp) with h6330 | h6330
                          · linarith only [h0, h6330, hlam]
                          · linarith only [h6288, h6330, hlam]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6287, h6308, h6311, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6312_1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6312_1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          rcases p6312_3 (m.d 0 2) (by simp) with h6336 | h6336
                          · linarith only [h4553, h6336, hlam]
                          · linarith only [h6287, h6336, hlam]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          rcases p6312_3 (m.d 0 2) (by simp) with h6339 | h6339
                          · linarith only [h4553, h6339, hlam]
                          · linarith only [h6288, h6339, hlam]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6287, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6305, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6308, hlam, p6312_1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6287, hc25, hlam, hphi, ht0b, ht5b, p6312_1, u0elo1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6288, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6306, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6309, hlam, p6312_1]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [h6310, hlam, p6312_0]
                        · have p6312_0 := h6312c.1
                          have p6312_1 := h6312c.2.1
                          have p6312_2 := h6312c.2.2.1
                          have p6312_3 := h6312c.2.2.2
                          linarith only [hlam, p6312_0]
                      · linarith only [h0, h6287, h6291, h6310, h6311, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6353 | h6353
                      · linarith only [h6308, h6310, h6353, hlam]
                      · rcases h2bigk with h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c | h6355c
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h0, hlam, p6355_1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h4553, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          rcases p6355_3 (m.d 0 2) (by simp) with h6359 | h6359
                          · rcases p6355_3 (m.d 1 2) (by simp) with h6360 | h6360
                            · rcases p6355_3 (m.d 2 3) (by simp) with h6361 | h6361
                              · rcases p6355_3 (m.d 2 4) (by simp) with h6362 | h6362
                                · linarith only [h6362, hlam, p6355_0]
                                · rcases p6355_3 (m.d 2 5) (by simp) with h6364 | h6364
                                  · linarith only [h6288, h6364, hlam]
                                  · linarith only [h6310, h6364, hlam]
                              · linarith only [h6308, h6361, hlam]
                            · linarith only [h6305, h6360, hlam]
                          · linarith only [h6359, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          rcases p6355_3 (m.d 0 2) (by simp) with h6370 | h6370
                          · rcases p6355_3 (m.d 1 2) (by simp) with h6371 | h6371
                            · rcases p6355_3 (m.d 2 3) (by simp) with h6372 | h6372
                              · rcases p6355_3 (m.d 2 4) (by simp) with h6373 | h6373
                                · linarith only [h6287, h6373, hlam]
                                · rcases p6355_3 (m.d 2 5) (by simp) with h6375 | h6375
                                  · linarith only [h6375, hlam, p6355_0]
                                  · rcases h5bigk with h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c | h6377c
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h2858, hlam, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6308, h6310, hc34, hlam, hphi, ht0b, ht45, ht5b, p6377_1, u0elo4]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h2858, h6291, h6305, h6307, h6353, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h2858, h6291, h6305, h6307, h6308, h6310, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6291, h6305, h6307, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6291, h6305, h6307, h6308, h6310, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6291, h6305, h6307, h6353, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6291, h6305, h6307, h6308, h6310, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6288, hlam, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6306, hlam, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h0, h6291, h6353, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6355_1, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6310, hlam, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6289, hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6309, hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6353, hlam, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6290, hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6307, hlam, p6377_0]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h6290, hc25, hlam, hphi, ht0b, ht5b, p6377_1, u0elo3]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [h0, h6287, h6290, h6291, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p6377_1]
                                    · have p6377_0 := h6377c.1
                                      have p6377_1 := h6377c.2.1
                                      have p6377_2 := h6377c.2.2.1
                                      have p6377_3 := h6377c.2.2.2
                                      linarith only [hlam, p6377_0]
                              · linarith only [h6309, h6372, hlam]
                            · linarith only [h6306, h6371, hlam]
                          · linarith only [h6370, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6291, hc02, hc23, hlam, hphi, p6355_1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6291, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          rcases p6355_3 (m.d 0 2) (by simp) with h6409 | h6409
                          · linarith only [h0, h6409, hlam]
                          · linarith only [h6287, h6409, hlam]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          rcases p6355_3 (m.d 0 2) (by simp) with h6412 | h6412
                          · linarith only [h0, h6412, hlam]
                          · linarith only [h6288, h6412, hlam]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6287, h6290, h6308, h6310, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6355_1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6355_1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h4553, h6287, h6290, h6310, hlam, p6355_2]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          rcases p6355_3 (m.d 0 2) (by simp) with h6419 | h6419
                          · linarith only [h4553, h6419, hlam]
                          · linarith only [h6288, h6419, hlam]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6287, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6305, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6308, hlam, p6355_1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6310, hlam, p6355_1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6288, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6306, hlam, p6355_0]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6309, hlam, p6355_1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [h6288, h6308, hc34, hlam, hphi, ht0b, ht45, ht5b, p6355_1, u0elo1]
                        · have p6355_0 := h6355c.1
                          have p6355_1 := h6355c.2.1
                          have p6355_2 := h6355c.2.2.1
                          have p6355_3 := h6355c.2.2.2
                          linarith only [hlam, p6355_0]
                  · linarith only [h0, h6291, h6309, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h6291, h6308, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h2858, h6287, h6290, h6291, h6307, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h6288, h6306, hlam]
          · linarith only [h0, h6287, h6305, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6437 | h6437
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6438 | h6438
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6439 | h6439
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6440 | h6440
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6441 | h6441
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6442 | h6442
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6443 | h6443
                    · linarith only [h6287, h6290, h6443, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6445 | h6445
                      · linarith only [h6287, h6290, h6441, h6445, hlam]
                      · rcases h2bigk with h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c | h6447c
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h0, hlam, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h4553, hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h4553, h6437, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h4553, h6437, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          rcases p6447_3 (m.d 0 2) (by simp) with h6453 | h6453
                          · linarith only [h0, h6453, hlam]
                          · rcases p6447_3 (m.d 1 2) (by simp) with h6455 | h6455
                            · rcases p6447_3 (m.d 2 3) (by simp) with h6456 | h6456
                              · linarith only [h6437, h6456, hlam]
                              · linarith only [h4553, h6456, hlam]
                            · linarith only [h0, h6455, hlam]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h0, h4553, hc01, hc12, hlam, hphi, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h4553, h6288, h6437, h6443, hlam, p6447_2]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h4553, h6288, h6437, hlam, p6447_2]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6288, h6437, h6441, h6443, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6437, hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          rcases p6447_3 (m.d 0 2) (by simp) with h6467 | h6467
                          · linarith only [h4553, h6467, hlam]
                          · linarith only [h6287, h6467, hlam]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          rcases p6447_3 (m.d 0 2) (by simp) with h6470 | h6470
                          · linarith only [h4553, h6470, hlam]
                          · linarith only [h6288, h6470, hlam]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6287, hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6438, hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6441, hlam, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6443, hlam, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6288, hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6439, hlam, p6447_0]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6442, hlam, p6447_1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [h6288, h6441, hc34, hlam, hphi, ht0b, ht45, ht5b, p6447_1, u0elo1]
                        · have p6447_0 := h6447c.1
                          have p6447_1 := h6447c.2.1
                          have p6447_2 := h6447c.2.2.1
                          have p6447_3 := h6447c.2.2.2
                          linarith only [hlam, p6447_0]
                  · linarith only [h4553, h6289, h6442, hlam]
                · linarith only [h4553, h6287, h6441, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6485 | h6485
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6486 | h6486
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6487 | h6487
                    · linarith only [h2858, h6287, h6440, h6487, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6489 | h6489
                      · linarith only [h2858, h4553, h6288, h6437, h6440, h6485, h6487, h6489, hc01, hc12, hlam, hphi]
                      · rcases h2bigk with h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c | h6491c
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h0, hlam, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h4553, hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h4553, h6437, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h4553, h6437, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          rcases p6491_3 (m.d 0 2) (by simp) with h6497 | h6497
                          · linarith only [h0, h6497, hlam]
                          · rcases p6491_3 (m.d 1 2) (by simp) with h6499 | h6499
                            · rcases p6491_3 (m.d 2 3) (by simp) with h6500 | h6500
                              · linarith only [h6437, h6500, hlam]
                              · linarith only [h4553, h6500, hlam]
                            · linarith only [h0, h6499, hlam]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h0, h4553, hc01, hc12, hlam, hphi, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h4553, h6288, h6437, h6487, hlam, p6491_2]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h4553, h6288, h6437, hlam, p6491_2]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6288, h6437, h6485, h6487, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6437, hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          rcases p6491_3 (m.d 0 2) (by simp) with h6511 | h6511
                          · linarith only [h4553, h6511, hlam]
                          · linarith only [h6287, h6511, hlam]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          rcases p6491_3 (m.d 0 2) (by simp) with h6514 | h6514
                          · linarith only [h4553, h6514, hlam]
                          · linarith only [h6288, h6514, hlam]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6287, hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6438, hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6485, hlam, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6487, hlam, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6288, hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6439, hlam, p6491_0]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6486, hlam, p6491_1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [h6288, h6485, hc34, hlam, hphi, ht0b, ht45, ht5b, p6491_1, u0elo1]
                        · have p6491_0 := h6491c.1
                          have p6491_1 := h6491c.2.1
                          have p6491_2 := h6491c.2.2.1
                          have p6491_3 := h6491c.2.2.2
                          linarith only [hlam, p6491_0]
                  · linarith only [h4553, h6289, h6486, hlam]
                · linarith only [h4553, h6287, h6485, hlam]
            · linarith only [h4553, h6288, h6439, hc12, hc23, hlam, hphi]
          · linarith only [h4553, h6287, h6437, h6438, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6531 | h6531
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6532 | h6532
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6533 | h6533
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6534 | h6534
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6535 | h6535
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6536 | h6536
                    · linarith only [h6287, h6290, h6536, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6538 | h6538
                      · linarith only [h6287, h6290, h6534, h6538, hlam]
                      · rcases h2bigk with h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c | h6540c
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h0, hlam, p6540_1]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h4553, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          rcases p6540_3 (m.d 0 2) (by simp) with h6544 | h6544
                          · rcases p6540_3 (m.d 1 2) (by simp) with h6545 | h6545
                            · rcases p6540_3 (m.d 2 3) (by simp) with h6546 | h6546
                              · rcases p6540_3 (m.d 2 4) (by simp) with h6547 | h6547
                                · linarith only [h6547, hlam, p6540_0]
                                · rcases p6540_3 (m.d 2 5) (by simp) with h6549 | h6549
                                  · linarith only [h6288, h6549, hlam]
                                  · linarith only [h6536, h6549, hlam]
                              · linarith only [h6534, h6546, hlam]
                            · linarith only [h6531, h6545, hlam]
                          · linarith only [h6544, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          rcases p6540_3 (m.d 0 2) (by simp) with h6555 | h6555
                          · rcases p6540_3 (m.d 1 2) (by simp) with h6556 | h6556
                            · rcases p6540_3 (m.d 2 3) (by simp) with h6557 | h6557
                              · rcases p6540_3 (m.d 2 4) (by simp) with h6558 | h6558
                                · linarith only [h6287, h6558, hlam]
                                · rcases p6540_3 (m.d 2 5) (by simp) with h6560 | h6560
                                  · linarith only [h6560, hlam, p6540_0]
                                  · rcases h5bigk with h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c | h6562c
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [hlam, p6562_0]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h2858, hlam, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6290, h6437, h6531, h6533, h6534, h6536, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6290, h6437, h6531, h6533, h6538, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6290, hlam, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h2858, hc01, hc15, hlam, hphi, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [hlam, p6562_0]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6437, h6532, h6534, h6536, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6437, h6531, h6533, h6538, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6437, h6531, h6533, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6288, hlam, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6532, hlam, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [hlam, p6562_0]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6538, hc34, hlam, hphi, ht0b, ht45, ht5b, p6540_1, p6562_1, u0elo1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6536, hlam, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6289, hlam, p6562_0]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6535, hlam, p6562_0]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [hlam, p6562_0]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6538, hlam, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6533, hlam, p6562_0]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6437, h6531, h6533, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [h6437, h6531, h6533, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p6562_1]
                                    · have p6562_0 := h6562c.1
                                      have p6562_1 := h6562c.2.1
                                      have p6562_2 := h6562c.2.2.1
                                      have p6562_3 := h6562c.2.2.2
                                      linarith only [hlam, p6562_0]
                              · linarith only [h6535, h6557, hlam]
                            · linarith only [h6532, h6556, hlam]
                          · linarith only [h6555, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6437, hc02, hc23, hlam, hphi, p6540_1]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6437, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          rcases p6540_3 (m.d 0 2) (by simp) with h6594 | h6594
                          · linarith only [h0, h6594, hlam]
                          · linarith only [h6287, h6594, hlam]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          rcases p6540_3 (m.d 0 2) (by simp) with h6597 | h6597
                          · linarith only [h0, h6597, hlam]
                          · linarith only [h6288, h6597, hlam]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          rcases p6540_3 (m.d 0 2) (by simp) with h6600 | h6600
                          · linarith only [h6600, hlam, p6540_0]
                          · rcases p6540_3 (m.d 1 2) (by simp) with h6602 | h6602
                            · linarith only [h6437, h6602, hlam]
                            · linarith only [h0, h6602, hlam]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6287, h6290, h6531, h6533, h6534, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6540_1]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6287, h6290, h6437, h6531, h6533, hlam, p6540_2]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          rcases p6540_3 (m.d 0 2) (by simp) with h6608 | h6608
                          · linarith only [h4553, h6608, hlam]
                          · linarith only [h6288, h6608, hlam]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6287, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6531, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6534, hlam, p6540_1]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6536, hlam, p6540_1]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6288, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6532, hlam, p6540_0]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6535, hlam, p6540_1]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [h6288, h6534, hc34, hlam, hphi, ht0b, ht45, ht5b, p6540_1, u0elo1]
                        · have p6540_0 := h6540c.1
                          have p6540_1 := h6540c.2.1
                          have p6540_2 := h6540c.2.2.1
                          have p6540_3 := h6540c.2.2.2
                          linarith only [hlam, p6540_0]
                  · linarith only [h6287, h6290, h6437, h6531, h6533, h6534, h6535, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h6290, h6437, h6531, h6533, h6534, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6623 | h6623
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6624 | h6624
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6625 | h6625
                    · linarith only [h2858, h6287, h6533, h6625, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6627 | h6627
                      · linarith only [h2858, h6533, h6623, h6627, hc01, hc23, hlam, hphi, ht12]
                      · rcases h2bigk with h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c | h6629c
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h0, hlam, p6629_1]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h4553, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          rcases p6629_3 (m.d 0 2) (by simp) with h6633 | h6633
                          · rcases p6629_3 (m.d 1 2) (by simp) with h6634 | h6634
                            · rcases p6629_3 (m.d 2 3) (by simp) with h6635 | h6635
                              · rcases p6629_3 (m.d 2 4) (by simp) with h6636 | h6636
                                · linarith only [h6636, hlam, p6629_0]
                                · rcases p6629_3 (m.d 2 5) (by simp) with h6638 | h6638
                                  · linarith only [h6288, h6638, hlam]
                                  · linarith only [h6625, h6638, hlam]
                              · linarith only [h6623, h6635, hlam]
                            · linarith only [h6531, h6634, hlam]
                          · linarith only [h6633, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          rcases p6629_3 (m.d 0 2) (by simp) with h6644 | h6644
                          · rcases p6629_3 (m.d 1 2) (by simp) with h6645 | h6645
                            · rcases p6629_3 (m.d 2 3) (by simp) with h6646 | h6646
                              · rcases p6629_3 (m.d 2 4) (by simp) with h6647 | h6647
                                · linarith only [h6287, h6647, hlam]
                                · rcases p6629_3 (m.d 2 5) (by simp) with h6649 | h6649
                                  · linarith only [h6649, hlam, p6629_0]
                                  · rcases h5bigk with h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h2858, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6625, hc24, hlam, hphi, ht0b, ht45, ht5b, p6651_1, u0elo4]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht0b, ht5b, p6651_1, u0elo4]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6290, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, h2858, h6437, h6533, h6623, h6625, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p6629_1, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6437, h6532, h6623, h6625, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6437, h6532, h6627, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6533, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6288, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6532, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, h6437, h6627, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6629_1, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6625, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6289, hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6624, hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6627, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h2858, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6623, h6625, hc34, hc45, hlam, hphi, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6627, hc34, hc45, hlam, hphi, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                              · linarith only [h6624, h6646, hlam]
                            · linarith only [h6532, h6645, hlam]
                          · linarith only [h6644, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6437, hc02, hc23, hlam, hphi, p6629_1]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6437, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          rcases p6629_3 (m.d 0 2) (by simp) with h6683 | h6683
                          · linarith only [h0, h6683, hlam]
                          · linarith only [h6287, h6683, hlam]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          rcases p6629_3 (m.d 0 2) (by simp) with h6686 | h6686
                          · linarith only [h0, h6686, hlam]
                          · linarith only [h6288, h6686, hlam]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          rcases p6629_3 (m.d 0 2) (by simp) with h6689 | h6689
                          · linarith only [h6689, hlam, p6629_0]
                          · rcases p6629_3 (m.d 1 2) (by simp) with h6691 | h6691
                            · linarith only [h6437, h6691, hlam]
                            · linarith only [h0, h6691, hlam]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6629_1]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          rcases p6629_3 (m.d 0 2) (by simp) with h6696 | h6696
                          · linarith only [h4553, h6696, hlam]
                          · linarith only [h6287, h6696, hlam]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          rcases p6629_3 (m.d 0 2) (by simp) with h6699 | h6699
                          · linarith only [h4553, h6699, hlam]
                          · linarith only [h6288, h6699, hlam]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6287, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6531, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6623, hlam, p6629_1]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6625, hlam, p6629_1]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6288, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6532, hlam, p6629_0]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6624, hlam, p6629_1]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [h6288, h6623, hc34, hlam, hphi, ht0b, ht45, ht5b, p6629_1, u0elo1]
                        · have p6629_0 := h6629c.1
                          have p6629_1 := h6629c.2.1
                          have p6629_2 := h6629c.2.2.1
                          have p6629_3 := h6629c.2.2.2
                          linarith only [hlam, p6629_0]
                  · linarith only [h4553, h6289, h6624, hlam]
                · linarith only [h2858, h6437, h6532, h6623, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h6288, h6532, hlam]
          · linarith only [h0, h6287, h6531, hlam]
    · linarith only [h4553, h6288, h6289, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6717 | h6717
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6718 | h6718
      · linarith only [h6287, h6288, h6718, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6720 | h6720
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6721 | h6721
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6722 | h6722
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6723 | h6723
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6724 | h6724
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6725 | h6725
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6726 | h6726
                    · linarith only [h6287, h6718, h6726, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6728 | h6728
                      · linarith only [h6287, h6288, h6724, h6726, h6728, hlam]
                      · rcases h2bigk with h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c | h6730c
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h0, hlam, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h4553, hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6288, h6721, h6723, h6724, h6726, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6288, hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          rcases p6730_3 (m.d 0 2) (by simp) with h6736 | h6736
                          · linarith only [h0, h6736, hlam]
                          · rcases p6730_3 (m.d 1 2) (by simp) with h6738 | h6738
                            · rcases p6730_3 (m.d 2 3) (by simp) with h6739 | h6739
                              · linarith only [h6720, h6739, hlam]
                              · linarith only [h4553, h6739, hlam]
                            · linarith only [h0, h6738, hlam]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h0, h4553, hc01, hc12, hlam, hphi, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6287, h6288, h6721, h6723, h6726, hlam, p6730_2]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6287, h6288, h6724, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6287, h6720, h6724, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6720, hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          rcases p6730_3 (m.d 0 2) (by simp) with h6750 | h6750
                          · linarith only [h4553, h6750, hlam]
                          · linarith only [h6287, h6750, hlam]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6287, h6288, h6720, h6724, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6287, hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6721, hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6724, hlam, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6726, hlam, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6287, h6723, h6724, h6726, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6722, hlam, p6730_0]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [h6725, hlam, p6730_1]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          rcases p6730_3 (m.d 0 2) (by simp) with h6762 | h6762
                          · linarith only [h6288, h6762, hlam]
                          · linarith only [h6287, h6762, hlam]
                        · have p6730_0 := h6730c.1
                          have p6730_1 := h6730c.2.1
                          have p6730_2 := h6730c.2.2.1
                          have p6730_3 := h6730c.2.2.2
                          linarith only [hlam, p6730_0]
                  · linarith only [h4553, h6717, h6725, hlam]
                · linarith only [h4553, h6287, h6724, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6768 | h6768
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6769 | h6769
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6770 | h6770
                    · linarith only [h6287, h6723, h6770, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6772 | h6772
                      · linarith only [h6287, h6288, h6722, h6723, h6768, h6772, hlam]
                      · rcases h2bigk with h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c | h6774c
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h0, hlam, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h4553, hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6288, h6720, h6769, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6288, hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          rcases p6774_3 (m.d 0 2) (by simp) with h6780 | h6780
                          · linarith only [h0, h6780, hlam]
                          · rcases p6774_3 (m.d 1 2) (by simp) with h6782 | h6782
                            · rcases p6774_3 (m.d 2 3) (by simp) with h6783 | h6783
                              · linarith only [h6720, h6783, hlam]
                              · linarith only [h4553, h6783, hlam]
                            · linarith only [h0, h6782, hlam]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h0, h6288, h6769, hc01, hc12, hlam, hphi, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6287, h6288, h6720, h6769, hlam, p6774_2]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6287, h6288, h6768, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6287, h6720, h6768, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6720, hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          rcases p6774_3 (m.d 0 2) (by simp) with h6794 | h6794
                          · linarith only [h4553, h6794, hlam]
                          · linarith only [h6287, h6794, hlam]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6287, h6288, h6720, h6768, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6287, hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6721, hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6768, hlam, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6770, hlam, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6287, h6722, h6723, h6768, hc34, hc45, hlam, hphi, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6722, hlam, p6774_0]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [h6769, hlam, p6774_1]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          rcases p6774_3 (m.d 0 2) (by simp) with h6806 | h6806
                          · linarith only [h6288, h6806, hlam]
                          · linarith only [h6287, h6806, hlam]
                        · have p6774_0 := h6774c.1
                          have p6774_1 := h6774c.2.1
                          have p6774_2 := h6774c.2.2.1
                          have p6774_3 := h6774c.2.2.2
                          linarith only [hlam, p6774_0]
                  · linarith only [h4553, h6287, h6717, h6768, h6769, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                · linarith only [h4553, h6287, h6768, hlam]
            · linarith only [h4553, h6720, h6722, hc02, hc25, hlam, hphi]
          · linarith only [h4553, h6287, h6720, h6721, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6814 | h6814
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6815 | h6815
            · linarith only [h6287, h6288, h6720, h6815, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6817 | h6817
              · linarith only [h6814, h6815, h6817, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6819 | h6819
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6820 | h6820
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6821 | h6821
                    · linarith only [h6287, h6817, h6821, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6823 | h6823
                      · linarith only [h0, h6815, h6821, h6823, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h2bigk with h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c | h6825c
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h0, hlam, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h4553, hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h0, h6815, h6819, h6821, hc34, hc45, hlam, hphi, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6288, hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6815, h6820, hc02, hc23, hlam, hphi, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6720, hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6815, h6819, h6821, hc34, hc45, hlam, hphi, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6815, hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          rcases p6825_3 (m.d 0 2) (by simp) with h6836 | h6836
                          · linarith only [h6836, hlam, p6825_0]
                          · rcases p6825_3 (m.d 1 2) (by simp) with h6838 | h6838
                            · linarith only [h6720, h6838, hlam]
                            · linarith only [h0, h6838, hlam]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          rcases p6825_3 (m.d 0 2) (by simp) with h6843 | h6843
                          · linarith only [h4553, h6843, hlam]
                          · linarith only [h6287, h6843, hlam]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h2858, h6815, hc01, hc23, hlam, hphi, ht12, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6287, hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6814, hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6819, hlam, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [hlam, p6825_0]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6821, hlam, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6287, h6819, h6821, hc34, hc45, hlam, hphi, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h0, h6820, hc01, hc23, hlam, hphi, ht12, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [h6820, hlam, p6825_1]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          rcases p6825_3 (m.d 0 2) (by simp) with h6855 | h6855
                          · linarith only [h6288, h6855, hlam]
                          · linarith only [h6287, h6855, hlam]
                        · have p6825_0 := h6825c.1
                          have p6825_1 := h6825c.2.1
                          have p6825_2 := h6825c.2.2.1
                          have p6825_3 := h6825c.2.2.2
                          linarith only [hlam, p6825_0]
                  · linarith only [h4553, h6287, h6717, h6819, h6820, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                · linarith only [h0, h6720, h6819, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h0, h6287, h6814, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6862 | h6862
      · linarith only [h6287, h6288, h6862, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6864 | h6864
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6865 | h6865
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6866 | h6866
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6867 | h6867
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6868 | h6868
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6869 | h6869
                  · linarith only [h4553, h6287, h6717, h6864, h6869, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6871 | h6871
                    · linarith only [h6287, h6862, h6871, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6873 | h6873
                      · linarith only [h4553, h6287, h6868, h6869, h6871, h6873, hlam]
                      · linarith only [h4553, h6287, h6865, h6867, h6869, h6873, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h4553, h6287, h6868, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6877 | h6877
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6878 | h6878
                  · linarith only [h4553, h6287, h6717, h6864, h6877, h6878, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6880 | h6880
                    · linarith only [h6287, h6867, h6880, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6882 | h6882
                      · linarith only [h6288, h6866, h6867, h6877, h6878, h6882, hc02, hc35, hlam, hphi, ht23]
                      · linarith only [h4553, h6287, h6877, h6878, h6882, hc34, hc45, hlam, hphi]
                · linarith only [h4553, h6287, h6877, hlam]
            · linarith only [h4553, h6287, h6864, h6866, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h4553, h6287, h6864, h6865, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6888 | h6888
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6889 | h6889
            · linarith only [h6288, h6864, h6889, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6891 | h6891
              · linarith only [h6888, h6889, h6891, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6893 | h6893
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6894 | h6894
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6895 | h6895
                    · linarith only [h6287, h6891, h6895, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6897 | h6897
                      · linarith only [h4553, h6287, h6717, h6893, h6894, h6895, h6897, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases h2bigk with h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c | h6899c
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h0, hlam, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h4553, hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h4553, h6717, h6893, h6894, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6288, hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6889, hc02, hc25, hlam, hphi, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6864, hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6889, h6893, h6895, hc34, hc45, hlam, hphi, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6889, hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          rcases p6899_3 (m.d 0 2) (by simp) with h6910 | h6910
                          · linarith only [h6910, hlam, p6899_0]
                          · rcases p6899_3 (m.d 1 2) (by simp) with h6912 | h6912
                            · linarith only [h6864, h6912, hlam]
                            · linarith only [h0, h6912, hlam]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h4553, h6287, h6717, h6894, hlam, p6899_2]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6287, h6288, h6893, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6287, hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6888, hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6893, hlam, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [hlam, p6899_0]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6895, hlam, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6287, h6893, h6895, hc34, hc45, hlam, hphi, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [h6894, hlam, p6899_1]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          rcases p6899_3 (m.d 0 2) (by simp) with h6927 | h6927
                          · linarith only [h6288, h6927, hlam]
                          · linarith only [h6287, h6927, hlam]
                        · have p6899_0 := h6899c.1
                          have p6899_1 := h6899c.2.1
                          have p6899_2 := h6899c.2.2.1
                          have p6899_3 := h6899c.2.2.2
                          linarith only [hlam, p6899_0]
                  · linarith only [h0, h6864, h6894, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h6864, h6893, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h0, h6287, h6888, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]

end R2N4
