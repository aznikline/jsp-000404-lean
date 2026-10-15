import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LI_L_R_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h282 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h283 | h283
  · rcases m.htr 0 1 5 (by decide) (by decide) with h284 | h284
    · rcases m.htr 0 2 3 (by decide) (by decide) with h285 | h285
      · rcases m.htr 0 2 4 (by decide) (by decide) with h286 | h286
        · rcases m.htr 0 2 5 (by decide) (by decide) with h287 | h287
          · rcases m.htr 0 3 4 (by decide) (by decide) with h288 | h288
            · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
              · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                · rcases m.htr 1 2 3 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h295 | h295
                          · linarith only [h0, h282, h291, h292, h295, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h282, h291, h292, h294, h295, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h288, h290, h294, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
                      · linarith only [h0, h282, h289, h292, h293, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h282, h288, h292, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h284, h287, h291, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                        · linarith only [h286, h290, h305, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                          · linarith only [h286, h290, h307, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h0bigk with h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h0, hlam, p309_1]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h0, h282, h302, h304, h305, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p309_1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h0, h286, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p309_1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h0, h286, h290, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p309_1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h282, h302, h304, h305, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p309_1, u0elo1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h282, h302, h304, h305, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p309_1, u0elo1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h286, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p309_1, u0elo1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h286, h290, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p309_1, u0elo1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h282, hlam, p309_1]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h285, hlam, p309_1]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h286, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p309_1, u0elo2, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h0, h282, h286, h290, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p309_1, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h283, hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h286, hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h288, hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h290, hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h284, hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h287, hlam, p309_1]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h289, hlam, p309_0]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [h286, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p309_1, u0elo4, u2ehi3]
                            · have p309_0 := h309c.1
                              have p309_1 := h309c.2.1
                              have p309_2 := h309c.2.2.1
                              have p309_3 := h309c.2.2.2
                              linarith only [hlam, p309_0]
                      · linarith only [h0, h282, h289, h304, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h282, h288, h303, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h283, h286, h302, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h338 | h338
                · linarith only [h288, h289, h338, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
                      · linarith only [h0, h282, h289, h340, h342, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                        · linarith only [h0, h282, h283, h338, h340, h341, h344, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h346 | h346
                          · linarith only [h0, h282, h338, h340, h341, h346, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases h0bigk with h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h0, hlam, p348_1]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h0, h282, h340, h341, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p348_1]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h0, h286, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p348_1, u2ehi3]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h0, h282, h289, h340, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p348_1, u2ehi2]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h282, h340, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p348_1, u0elo1, u2ehi2]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h282, h340, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p348_1, u0elo1, u2ehi2]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h286, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p348_1, u0elo1, u2ehi3]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h282, h289, h340, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p348_1, u0elo1, u2ehi2]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h282, hlam, p348_1]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h285, hlam, p348_1]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h286, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p348_1, u0elo2, u2ehi3]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h289, hlam, p348_1]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h283, hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h286, hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h288, hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h338, hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h284, hlam, p348_0]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h287, hlam, p348_1]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h282, h340, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p348_1, u0elo4, u2ehi2]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [h0, h284, h286, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p348_1, u2ehi3]
                            · have p348_0 := h348c.1
                              have p348_1 := h348c.2.1
                              have p348_2 := h348c.2.2.1
                              have p348_3 := h348c.2.2.2
                              linarith only [hlam, p348_0]
                    · linarith only [h288, h341, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h283, h286, h340, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h376 | h376
              · rcases m.htr 0 4 5 (by decide) (by decide) with h377 | h377
                · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
                    · linarith only [h282, h288, h378, h379, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
                          · rcases h0bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h0, hlam, p384_1]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h0, h282, h378, h381, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h0, h282, h288, h378, h381, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h0, h287, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h282, h378, h381, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u0elo1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h282, h378, h381, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u0elo1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h282, h288, h378, h381, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u0elo1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h287, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u0elo1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h282, hlam, p384_1]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h285, hlam, p384_1]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h288, hlam, p384_1]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h287, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u0elo2, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h283, hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h286, hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h282, h378, h381, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u0elo3, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h0, h283, h287, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi4]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h284, hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h287, hlam, p384_1]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h376, hlam, p384_0]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [h377, hlam, p384_1]
                            · have p384_0 := h384c.1
                              have p384_1 := h384c.2.1
                              have p384_2 := h384c.2.2.1
                              have p384_3 := h384c.2.2.2
                              linarith only [hlam, p384_0]
                          · linarith only [h282, h288, h378, h381, h383, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · linarith only [h377, h379, h381, h382, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi4]
                      · linarith only [h376, h381, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h284, h287, h378, hc23, hlam, hphi, u2ehi4]
                · linarith only [h288, h376, h377, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
                · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h417 | h417
                    · linarith only [h282, h288, h416, h417, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
                      · linarith only [h282, h376, h416, h419, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
                          · rcases h0bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h0, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h0, h282, h416, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p423_1, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h0, h286, h419, h421, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p423_1, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h0, h287, h419, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p423_1, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h282, h416, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1, u0elo1, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h282, h416, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1, u0elo1, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h286, h419, h421, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1, u0elo1, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h287, h419, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1, u0elo1, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h282, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h285, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h288, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h376, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h283, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h286, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h282, h416, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1, u0elo3, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h282, h283, h376, h416, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1, u0elo0, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h284, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h287, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h282, h416, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p423_1, u0elo4, u2ehi2]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h415, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                          · linarith only [h286, h288, h421, h422, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h415, h417, h421, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi2]
                  · linarith only [h0, h285, h416, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
                    · linarith only [h282, h288, h452, h453, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                      · linarith only [h282, h376, h452, h455, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                        · linarith only [h286, h415, h457, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h459 | h459
                          · linarith only [h282, h288, h415, h452, h459, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h282, h288, h452, h459, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h283, h286, h452, hc23, hlam, hphi, u2ehi3]
          · linarith only [h285, h287, hc25, hlam, hphi, u2ehi2]
        · linarith only [h285, h286, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h282, h285, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h466 | h466
      · rcases m.htr 0 2 4 (by decide) (by decide) with h467 | h467
        · rcases m.htr 0 2 5 (by decide) (by decide) with h468 | h468
          · rcases m.htr 0 3 4 (by decide) (by decide) with h469 | h469
            · rcases m.htr 0 3 5 (by decide) (by decide) with h470 | h470
              · linarith only [h282, h284, h470, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h472 | h472
                · linarith only [h282, h284, h469, h472, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h476 | h476
                      · linarith only [h282, h470, h474, h476, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                        · linarith only [h282, h284, h472, h474, h475, h478, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h480 | h480
                          · linarith only [h282, h284, h472, h474, h475, h480, hlam]
                          · rcases h0bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h0, hlam, p482_1]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h282, h284, h468, h474, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h284, h467, h468, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h284, hlam, p482_1]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h282, h474, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h282, h474, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h467, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h282, h284, h474, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h282, hlam, p482_1]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h466, hlam, p482_1]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h467, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo2, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h470, hlam, p482_1]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h283, hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h467, hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h469, hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h472, hlam, p482_0]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h282, h474, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo4, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h468, hlam, p482_1]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h282, h468, h474, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [h467, h468, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p482_1, u0elo1, u2ehi3]
                            · have p482_0 := h482c.1
                              have p482_1 := h482c.2.1
                              have p482_2 := h482c.2.2.1
                              have p482_3 := h482c.2.2.2
                              linarith only [hlam, p482_0]
                    · linarith only [h469, h475, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h468, h474, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h510 | h510
              · linarith only [h283, h284, h469, h510, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                · linarith only [h283, h284, h512, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h514 | h514
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
                    · linarith only [h282, h469, h514, h515, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h517 | h517
                      · linarith only [h282, h284, h510, h514, h517, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h519 | h519
                        · linarith only [h282, h469, h512, h514, h519, hc24, hlam, hphi, u2ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h521 | h521
                          · linarith only [h282, h469, h512, h514, h521, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h282, h469, h514, h521, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h468, h514, hc23, hlam, hphi, u2ehi4]
          · linarith only [h466, h468, hc25, hlam, hphi, u2ehi2]
        · linarith only [h466, h467, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h282, h466, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h528 | h528
    · rcases m.htr 0 2 3 (by decide) (by decide) with h529 | h529
      · rcases m.htr 0 2 4 (by decide) (by decide) with h530 | h530
        · rcases m.htr 0 2 5 (by decide) (by decide) with h531 | h531
          · rcases m.htr 0 3 4 (by decide) (by decide) with h532 | h532
            · linarith only [h282, h283, h532, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
              · rcases m.htr 0 4 5 (by decide) (by decide) with h535 | h535
                · rcases m.htr 1 2 3 (by decide) (by decide) with h536 | h536
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
                    · linarith only [h282, h532, h536, h537, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h539 | h539
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h541 | h541
                          · rcases h0bigk with h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c | h542c
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [hlam, p542_0]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h0, hlam, p542_1]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h282, h283, h530, h536, h539, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h283, hlam, p542_1]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h283, h530, h531, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h282, h536, h539, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [hlam, p542_0]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h282, h536, h539, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h282, h283, h536, h539, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h531, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h282, hlam, p542_1]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h529, hlam, p542_1]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [hlam, p542_0]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h532, hlam, p542_1]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h531, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo2, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h282, h536, h539, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo3, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h530, hlam, p542_0]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h282, h530, h536, h539, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [hlam, p542_0]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h530, h531, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p542_1, u0elo1, u2ehi4]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h528, hlam, p542_0]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h531, hlam, p542_1]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h534, hlam, p542_0]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [h535, hlam, p542_1]
                            · have p542_0 := h542c.1
                              have p542_1 := h542c.2.1
                              have p542_2 := h542c.2.2.1
                              have p542_3 := h542c.2.2.2
                              linarith only [hlam, p542_0]
                          · linarith only [h282, h532, h536, h539, h541, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · linarith only [h532, h534, h535, h540, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h534, h539, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h0, h529, h536, hlam]
                · linarith only [h282, h283, h534, h535, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h573 | h573
                · rcases m.htr 1 2 3 (by decide) (by decide) with h574 | h574
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
                    · linarith only [h282, h532, h574, h575, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h577 | h577
                      · linarith only [h282, h534, h574, h577, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h579 | h579
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h580 | h580
                          · rcases h0bigk with h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h0, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h283, h530, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h283, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h283, h530, h531, h577, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h283, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h531, h577, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h529, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h532, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h534, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo3, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h530, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h530, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h530, h534, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo1, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h528, hlam, p581_0]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h531, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h282, h574, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1, u0elo4, u2ehi2]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [h573, hlam, p581_1]
                            · have p581_0 := h581c.1
                              have p581_1 := h581c.2.1
                              have p581_2 := h581c.2.2.1
                              have p581_3 := h581c.2.2.2
                              linarith only [hlam, p581_0]
                          · linarith only [h282, h283, h532, h574, h579, h580, hc24, hlam, hphi, u2ehi2]
                        · linarith only [h573, h579, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                  · linarith only [h0, h529, h574, hlam]
                · linarith only [h283, h528, h573, hlam]
          · linarith only [h529, h531, hc25, hlam, hphi, u2ehi2]
        · linarith only [h529, h530, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h282, h529, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h614 | h614
      · rcases m.htr 0 2 4 (by decide) (by decide) with h615 | h615
        · rcases m.htr 0 2 5 (by decide) (by decide) with h616 | h616
          · rcases m.htr 0 3 4 (by decide) (by decide) with h617 | h617
            · linarith only [h282, h283, h617, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h619 | h619
              · linarith only [h282, h528, h619, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h621 | h621
                · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h623 | h623
                    · linarith only [h282, h617, h622, h623, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
                      · linarith only [h282, h528, h619, h622, h625, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h627 | h627
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                          · rcases h0bigk with h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [hlam, p629_0]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h0, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h528, h615, h621, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h283, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h528, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [hlam, p629_0]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h283, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h528, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h614, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [hlam, p629_0]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h617, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h619, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo3, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h615, hlam, p629_0]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h615, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [hlam, p629_0]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h528, h615, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo4, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h616, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h282, h616, h622, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p629_1, u0elo1, u2ehi2]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [h621, hlam, p629_1]
                            · have p629_0 := h629c.1
                              have p629_1 := h629c.2.1
                              have p629_2 := h629c.2.2.1
                              have p629_3 := h629c.2.2.2
                              linarith only [hlam, p629_0]
                          · linarith only [h615, h617, h627, h628, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h621, h627, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
                  · linarith only [h0, h614, h622, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h658 | h658
                  · linarith only [h282, h283, h621, h658, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h614, h658, hlam]
          · linarith only [h614, h616, hc25, hlam, hphi, u2ehi2]
        · linarith only [h614, h615, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h282, h614, hlam]

end R2N4
