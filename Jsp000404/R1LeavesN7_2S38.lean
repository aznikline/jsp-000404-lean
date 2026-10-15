import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S37

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25078 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25079 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25080 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 1 3 5 (by decide) (by decide) with h25284 | h25284
  · linarith only [h14396, h24656, h25080, h25284, hc01, hc34, hlam, hphi, ht12, ht23]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h25286 | h25286
    · rcases m.htr 2 3 4 (by decide) (by decide) with h25287 | h25287
      · linarith only [h14396, h25080, h25287, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h25289 | h25289
        · linarith only [h14396, h25284, h25289, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h25291 | h25291
          · rcases m.htr 3 4 5 (by decide) (by decide) with h25292 | h25292
            · rcases h0bigk with h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c | h25293c
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [hlam, p25293_0]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h0, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h14396, hlam, p25293_0]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h16915, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h18815, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25299 | h25299
                · linarith only [h0, h25299, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25301 | h25301
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25302 | h25302
                    · linarith only [h20408, h25302, hlam]
                    · linarith only [h14396, h25302, hlam]
                  · linarith only [h0, h25301, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [hlam, p25293_0]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25307 | h25307
                · linarith only [h0, h25307, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25309 | h25309
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25310 | h25310
                    · linarith only [h20408, h25310, hlam]
                    · rcases p25293_3 (m.d 0 4) (by simp) with h25312 | h25312
                      · linarith only [h20409, h25312, hlam]
                      · linarith only [h20411, h25312, hlam]
                  · linarith only [h20408, h25309, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25316 | h25316
                · linarith only [h0, h25316, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25318 | h25318
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25319 | h25319
                    · linarith only [h20408, h25319, hlam]
                    · rcases p25293_3 (m.d 0 4) (by simp) with h25321 | h25321
                      · linarith only [h20409, h25321, hlam]
                      · rcases p25293_3 (m.d 0 5) (by simp) with h25323 | h25323
                        · linarith only [h20410, h25323, hlam]
                        · rcases h2bigk with h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c | h25325c
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h0, hlam, p25325_1]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            rcases p25325_3 (m.d 0 2) (by simp) with h25328 | h25328
                            · rcases p25325_3 (m.d 1 2) (by simp) with h25329 | h25329
                              · rcases p25325_3 (m.d 2 3) (by simp) with h25330 | h25330
                                · linarith only [h25330, hlam, p25325_0]
                                · rcases p25325_3 (m.d 2 4) (by simp) with h25332 | h25332
                                  · linarith only [h20409, h25332, hlam]
                                  · linarith only [h25287, h25332, hlam]
                              · linarith only [h25077, h25329, hlam]
                            · linarith only [h25328, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            rcases p25325_3 (m.d 0 2) (by simp) with h25337 | h25337
                            · rcases p25325_3 (m.d 1 2) (by simp) with h25338 | h25338
                              · rcases p25325_3 (m.d 2 3) (by simp) with h25339 | h25339
                                · linarith only [h20408, h25339, hlam]
                                · rcases p25325_3 (m.d 2 4) (by simp) with h25341 | h25341
                                  · linarith only [h25341, hlam, p25325_0]
                                  · rcases p25325_3 (m.d 2 5) (by simp) with h25343 | h25343
                                    · linarith only [h20410, h25343, hlam]
                                    · rcases h3bigk with h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h14396, hlam, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h14396, h25284, h25292, hc23, hc34, hlam, hphi, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h20411, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h24656, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25284, h25292, hc03, hc34, hlam, hphi, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25284, h25292, hc23, hc34, hlam, hphi, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25080, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25284, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h20408, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25077, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25287, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25289, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h14396, h24656, hc01, hc34, hlam, hphi, ht12, ht23, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25292, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                              · linarith only [h25078, h25338, hlam]
                            · linarith only [h25337, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            rcases p25325_3 (m.d 0 2) (by simp) with h25373 | h25373
                            · rcases p25325_3 (m.d 1 2) (by simp) with h25374 | h25374
                              · rcases p25325_3 (m.d 2 3) (by simp) with h25375 | h25375
                                · linarith only [h20408, h25375, hlam]
                                · rcases p25325_3 (m.d 2 4) (by simp) with h25377 | h25377
                                  · linarith only [h20409, h25377, hlam]
                                  · linarith only [h25291, h25377, hlam]
                              · linarith only [h25079, h25374, hlam]
                            · linarith only [h25373, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p25293_1, p25325_1]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            rcases p25325_3 (m.d 0 2) (by simp) with h25384 | h25384
                            · linarith only [h0, h25384, hlam]
                            · linarith only [h20408, h25384, hlam]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            rcases p25325_3 (m.d 0 2) (by simp) with h25387 | h25387
                            · linarith only [h0, h25387, hlam]
                            · linarith only [h20409, h25387, hlam]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            rcases p25325_3 (m.d 0 2) (by simp) with h25390 | h25390
                            · linarith only [h0, h25390, hlam]
                            · linarith only [h20410, h25390, hlam]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h20408, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h25077, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h25287, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h25289, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h20409, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h25078, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h20409, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25293_1, p25325_1]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h0, h20409, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p25293_1, p25325_1]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h20410, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h25079, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h0, h20410, h25076, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25293_1, p25325_1]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [h25291, hlam, p25325_0]
                          · have p25325_0 := h25325c.1
                            have p25325_1 := h25325c.2.1
                            have p25325_2 := h25325c.2.2.1
                            have p25325_3 := h25325c.2.2.2
                            linarith only [hlam, p25325_0]
                  · linarith only [h20409, h25318, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25409 | h25409
                · linarith only [h0, h25409, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25411 | h25411
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25412 | h25412
                    · linarith only [h20408, h25412, hlam]
                    · rcases p25293_3 (m.d 0 4) (by simp) with h25414 | h25414
                      · linarith only [h20409, h25414, hlam]
                      · linarith only [h25076, h25414, hlam]
                  · linarith only [h20410, h25411, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h20411, hc01, hc34, hlam, hphi, ht12, ht23, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h20408, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [hlam, p25293_0]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h20411, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h24656, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25423 | h25423
                · linarith only [h16915, h25423, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25425 | h25425
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25426 | h25426
                    · linarith only [h20411, h25426, hlam]
                    · linarith only [h14396, h25426, hlam]
                  · linarith only [h0, h25425, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h20409, hlam, p25293_0]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25431 | h25431
                · linarith only [h16915, h25431, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25433 | h25433
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25434 | h25434
                    · linarith only [h20411, h25434, hlam]
                    · rcases p25293_3 (m.d 0 4) (by simp) with h25436 | h25436
                      · rcases p25293_3 (m.d 0 5) (by simp) with h25437 | h25437
                        · linarith only [h25076, h25437, hlam]
                        · linarith only [h24656, h25437, hlam]
                      · linarith only [h20411, h25436, hlam]
                  · linarith only [h20408, h25433, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [hlam, p25293_0]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25443 | h25443
                · linarith only [h16915, h25443, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25445 | h25445
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25446 | h25446
                    · linarith only [h20411, h25446, hlam]
                    · rcases p25293_3 (m.d 0 4) (by simp) with h25448 | h25448
                      · rcases p25293_3 (m.d 0 5) (by simp) with h25449 | h25449
                        · linarith only [h25076, h25449, hlam]
                        · rcases h2bigk with h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c | h25451c
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h0, hlam, p25451_1]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25454 | h25454
                            · rcases p25451_3 (m.d 1 2) (by simp) with h25455 | h25455
                              · rcases p25451_3 (m.d 2 3) (by simp) with h25456 | h25456
                                · linarith only [h25456, hlam, p25451_0]
                                · rcases p25451_3 (m.d 2 4) (by simp) with h25458 | h25458
                                  · linarith only [h20409, h25458, hlam]
                                  · linarith only [h25287, h25458, hlam]
                              · linarith only [h25077, h25455, hlam]
                            · linarith only [h25454, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25463 | h25463
                            · rcases p25451_3 (m.d 1 2) (by simp) with h25464 | h25464
                              · rcases p25451_3 (m.d 2 3) (by simp) with h25465 | h25465
                                · linarith only [h20408, h25465, hlam]
                                · rcases p25451_3 (m.d 2 4) (by simp) with h25467 | h25467
                                  · linarith only [h25467, hlam, p25451_0]
                                  · rcases p25451_3 (m.d 2 5) (by simp) with h25469 | h25469
                                    · linarith only [h20410, h25469, hlam]
                                    · rcases h3bigk with h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c | h25471c
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h14396, hlam, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h24656, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25293_1, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h20411, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h24656, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25284, h25292, hc03, hc34, hlam, hphi, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25284, h25292, hc23, hc34, hlam, hphi, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25080, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25284, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h20408, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25077, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25287, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25289, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h14396, h24656, hc01, hc34, hlam, hphi, ht12, ht23, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p25471_1]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [h25292, hlam, p25471_0]
                                      · have p25471_0 := h25471c.1
                                        have p25471_1 := h25471c.2.1
                                        have p25471_2 := h25471c.2.2.1
                                        have p25471_3 := h25471c.2.2.2
                                        linarith only [hlam, p25471_0]
                              · linarith only [h25078, h25464, hlam]
                            · linarith only [h25463, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25499 | h25499
                            · rcases p25451_3 (m.d 1 2) (by simp) with h25500 | h25500
                              · rcases p25451_3 (m.d 2 3) (by simp) with h25501 | h25501
                                · linarith only [h20408, h25501, hlam]
                                · rcases p25451_3 (m.d 2 4) (by simp) with h25503 | h25503
                                  · linarith only [h20409, h25503, hlam]
                                  · linarith only [h25291, h25503, hlam]
                              · linarith only [h25079, h25500, hlam]
                            · linarith only [h25499, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h14396, h20409, h24656, hc01, hc12, hlam, hphi, p25293_1, p25451_1]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25510 | h25510
                            · linarith only [h0, h25510, hlam]
                            · linarith only [h20408, h25510, hlam]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25513 | h25513
                            · linarith only [h0, h25513, hlam]
                            · linarith only [h20409, h25513, hlam]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25516 | h25516
                            · linarith only [h0, h25516, hlam]
                            · linarith only [h20410, h25516, hlam]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h20408, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h25077, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h25287, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h25289, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h20409, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h25078, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25526 | h25526
                            · rcases p25451_3 (m.d 1 2) (by simp) with h25527 | h25527
                              · rcases p25451_3 (m.d 2 3) (by simp) with h25528 | h25528
                                · linarith only [h25287, h25528, hlam]
                                · rcases p25451_3 (m.d 2 4) (by simp) with h25530 | h25530
                                  · rcases p25451_3 (m.d 2 5) (by simp) with h25531 | h25531
                                    · linarith only [h25291, h25531, hlam]
                                    · linarith only [h25289, h25531, hlam]
                                  · linarith only [h25287, h25530, hlam]
                              · linarith only [h25077, h25527, hlam]
                            · linarith only [h20408, h25526, hlam]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            rcases p25451_3 (m.d 0 2) (by simp) with h25538 | h25538
                            · rcases p25451_3 (m.d 1 2) (by simp) with h25539 | h25539
                              · rcases p25451_3 (m.d 2 3) (by simp) with h25540 | h25540
                                · linarith only [h25287, h25540, hlam]
                                · rcases p25451_3 (m.d 2 4) (by simp) with h25542 | h25542
                                  · rcases p25451_3 (m.d 2 5) (by simp) with h25543 | h25543
                                    · linarith only [h25291, h25543, hlam]
                                    · rcases h3bigk with h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c | h25545c
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h14396, hlam, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h24656, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25293_1, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h20411, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h24656, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h14396, hc01, hc13, hlam, hphi, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h25080, hc23, hc34, hlam, hphi, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h25080, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h25284, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h20408, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h25077, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h25287, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h25289, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h0, h14396, h20409, h24656, h25289, hc01, hc12, hc23, hc34, hlam, hphi, p25451_1, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h0, h14396, h20409, h25289, hc01, hc12, hc23, hc35, hlam, hphi, p25451_1, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h0, h14396, h20409, h25289, hc01, hc12, hc23, hc35, hlam, hphi, p25451_1, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p25545_1]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [h25292, hlam, p25545_0]
                                      · have p25545_0 := h25545c.1
                                        have p25545_1 := h25545c.2.1
                                        have p25545_2 := h25545c.2.2.1
                                        have p25545_3 := h25545c.2.2.2
                                        linarith only [hlam, p25545_0]
                                  · linarith only [h25291, h25542, hlam]
                              · linarith only [h25079, h25539, hlam]
                            · linarith only [h20410, h25538, hlam]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h20410, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h25079, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h16915, h20410, h25080, hc23, hc34, hlam, hphi, p25293_1, p25451_1]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [h25291, hlam, p25451_0]
                          · have p25451_0 := h25451c.1
                            have p25451_1 := h25451c.2.1
                            have p25451_2 := h25451c.2.2.1
                            have p25451_3 := h25451c.2.2.2
                            linarith only [hlam, p25451_0]
                      · linarith only [h25076, h25448, hlam]
                  · linarith only [h20410, h25445, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25581 | h25581
                · linarith only [h18815, h25581, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25583 | h25583
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25584 | h25584
                    · linarith only [h24656, h25584, hlam]
                    · linarith only [h14396, h25584, hlam]
                  · linarith only [h0, h25583, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h20410, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                rcases p25293_3 (m.d 0 1) (by simp) with h25589 | h25589
                · linarith only [h18815, h25589, hlam]
                · rcases p25293_3 (m.d 0 2) (by simp) with h25591 | h25591
                  · rcases p25293_3 (m.d 0 3) (by simp) with h25592 | h25592
                    · linarith only [h24656, h25592, hlam]
                    · rcases p25293_3 (m.d 0 4) (by simp) with h25594 | h25594
                      · rcases p25293_3 (m.d 0 5) (by simp) with h25595 | h25595
                        · rcases h2bigk with h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c | h25596c
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h0, hlam, p25596_1]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25599 | h25599
                            · rcases p25596_3 (m.d 1 2) (by simp) with h25600 | h25600
                              · rcases p25596_3 (m.d 2 3) (by simp) with h25601 | h25601
                                · linarith only [h25601, hlam, p25596_0]
                                · rcases p25596_3 (m.d 2 4) (by simp) with h25603 | h25603
                                  · linarith only [h20409, h25603, hlam]
                                  · linarith only [h25287, h25603, hlam]
                              · linarith only [h25077, h25600, hlam]
                            · linarith only [h25599, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25608 | h25608
                            · rcases p25596_3 (m.d 1 2) (by simp) with h25609 | h25609
                              · rcases p25596_3 (m.d 2 3) (by simp) with h25610 | h25610
                                · linarith only [h20408, h25610, hlam]
                                · rcases p25596_3 (m.d 2 4) (by simp) with h25612 | h25612
                                  · linarith only [h25612, hlam, p25596_0]
                                  · rcases p25596_3 (m.d 2 5) (by simp) with h25614 | h25614
                                    · linarith only [h20410, h25614, hlam]
                                    · rcases h3bigk with h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c | h25616c
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h14396, hlam, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h18815, h25080, h25286, hc23, hc34, hlam, hphi, p25293_1, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h20411, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h24656, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h14396, hc01, hc13, hlam, hphi, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h25080, hc23, hc34, hlam, hphi, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h25080, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h25284, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h20408, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h25077, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h25287, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h25289, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h14396, h24656, hc01, hc34, hlam, hphi, ht12, ht23, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p25616_1]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [h25292, hlam, p25616_0]
                                      · have p25616_0 := h25616c.1
                                        have p25616_1 := h25616c.2.1
                                        have p25616_2 := h25616c.2.2.1
                                        have p25616_3 := h25616c.2.2.2
                                        linarith only [hlam, p25616_0]
                              · linarith only [h25078, h25609, hlam]
                            · linarith only [h25608, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25644 | h25644
                            · rcases p25596_3 (m.d 1 2) (by simp) with h25645 | h25645
                              · rcases p25596_3 (m.d 2 3) (by simp) with h25646 | h25646
                                · linarith only [h20408, h25646, hlam]
                                · rcases p25596_3 (m.d 2 4) (by simp) with h25648 | h25648
                                  · linarith only [h20409, h25648, hlam]
                                  · linarith only [h25291, h25648, hlam]
                              · linarith only [h25079, h25645, hlam]
                            · linarith only [h25644, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h14396, h20410, hc01, hc12, hlam, hphi, p25293_1, p25596_1]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25655 | h25655
                            · linarith only [h0, h25655, hlam]
                            · linarith only [h20408, h25655, hlam]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25658 | h25658
                            · linarith only [h0, h25658, hlam]
                            · linarith only [h20409, h25658, hlam]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25661 | h25661
                            · linarith only [h0, h25661, hlam]
                            · linarith only [h20410, h25661, hlam]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h20408, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h25077, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h25287, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h25289, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h20409, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h25078, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25671 | h25671
                            · rcases p25596_3 (m.d 1 2) (by simp) with h25672 | h25672
                              · rcases p25596_3 (m.d 2 3) (by simp) with h25673 | h25673
                                · linarith only [h25287, h25673, hlam]
                                · rcases p25596_3 (m.d 2 4) (by simp) with h25675 | h25675
                                  · rcases p25596_3 (m.d 2 5) (by simp) with h25676 | h25676
                                    · linarith only [h25291, h25676, hlam]
                                    · linarith only [h25289, h25676, hlam]
                                  · linarith only [h25287, h25675, hlam]
                              · linarith only [h25077, h25672, hlam]
                            · linarith only [h20408, h25671, hlam]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25683 | h25683
                            · rcases p25596_3 (m.d 1 2) (by simp) with h25684 | h25684
                              · rcases p25596_3 (m.d 2 3) (by simp) with h25685 | h25685
                                · linarith only [h25287, h25685, hlam]
                                · rcases p25596_3 (m.d 2 4) (by simp) with h25687 | h25687
                                  · rcases p25596_3 (m.d 2 5) (by simp) with h25688 | h25688
                                    · linarith only [h25291, h25688, hlam]
                                    · rcases h3bigk with h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c | h25690c
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h14396, hlam, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25076, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25293_1, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h20411, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h24656, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h14396, hc01, hc13, hlam, hphi, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25080, hc23, hc34, hlam, hphi, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25080, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25284, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h20408, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25077, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25287, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25289, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h0, h14396, h20409, h24656, h25289, hc01, hc12, hc23, hc34, hlam, hphi, p25596_1, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h0, h14396, h20409, h25289, hc01, hc12, hc23, hc35, hlam, hphi, p25596_1, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h0, h14396, h20409, h25289, hc01, hc12, hc23, hc35, hlam, hphi, p25596_1, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p25690_1]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [h25292, hlam, p25690_0]
                                      · have p25690_0 := h25690c.1
                                        have p25690_1 := h25690c.2.1
                                        have p25690_2 := h25690c.2.2.1
                                        have p25690_3 := h25690c.2.2.2
                                        linarith only [hlam, p25690_0]
                                  · linarith only [h25291, h25687, hlam]
                              · linarith only [h25079, h25684, hlam]
                            · linarith only [h20410, h25683, hlam]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h20410, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h25079, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            rcases p25596_3 (m.d 0 2) (by simp) with h25721 | h25721
                            · rcases p25596_3 (m.d 1 2) (by simp) with h25722 | h25722
                              · rcases p25596_3 (m.d 2 3) (by simp) with h25723 | h25723
                                · linarith only [h25289, h25723, hlam]
                                · rcases p25596_3 (m.d 2 4) (by simp) with h25725 | h25725
                                  · rcases p25596_3 (m.d 2 5) (by simp) with h25726 | h25726
                                    · rcases h3bigk with h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c | h25727c
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h14396, hlam, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h16915, h25076, h25080, hc23, hc34, hlam, hphi, p25293_1, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h20411, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h24656, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h14396, hc01, hc13, hlam, hphi, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h25080, hc23, hc34, hlam, hphi, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h25080, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h25284, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h20408, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h25077, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h25287, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h25289, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h14396, h24656, hc01, hc34, hlam, hphi, ht12, ht23, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p25727_1]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [h25292, hlam, p25727_0]
                                      · have p25727_0 := h25727c.1
                                        have p25727_1 := h25727c.2.1
                                        have p25727_2 := h25727c.2.2.1
                                        have p25727_3 := h25727c.2.2.2
                                        linarith only [hlam, p25727_0]
                                    · linarith only [h25289, h25726, hlam]
                                  · linarith only [h25287, h25725, hlam]
                              · linarith only [h25077, h25722, hlam]
                            · linarith only [h20408, h25721, hlam]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [h25291, hlam, p25596_0]
                          · have p25596_0 := h25596c.1
                            have p25596_1 := h25596c.2.1
                            have p25596_2 := h25596c.2.2.1
                            have p25596_3 := h25596c.2.2.2
                            linarith only [hlam, p25596_0]
                        · linarith only [h24656, h25595, hlam]
                      · linarith only [h20411, h25594, hlam]
                  · linarith only [h20408, h25591, hlam]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [h25076, hlam, p25293_1]
              · have p25293_0 := h25293c.1
                have p25293_1 := h25293c.2.1
                have p25293_2 := h25293c.2.2.1
                have p25293_3 := h25293c.2.2.2
                linarith only [hlam, p25293_0]
            · linarith only [h16915, h25076, h25080, h25292, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h25765 | h25765
            · rcases h0bigk with h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c | h25766c
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [hlam, p25766_0]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h0, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h14396, hlam, p25766_0]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h16915, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h18815, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                rcases p25766_3 (m.d 0 1) (by simp) with h25772 | h25772
                · linarith only [h0, h25772, hlam]
                · rcases p25766_3 (m.d 0 2) (by simp) with h25774 | h25774
                  · rcases p25766_3 (m.d 0 3) (by simp) with h25775 | h25775
                    · linarith only [h20408, h25775, hlam]
                    · linarith only [h14396, h25775, hlam]
                  · linarith only [h0, h25774, hlam]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [hlam, p25766_0]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                rcases p25766_3 (m.d 0 1) (by simp) with h25780 | h25780
                · linarith only [h0, h25780, hlam]
                · rcases p25766_3 (m.d 0 2) (by simp) with h25782 | h25782
                  · rcases p25766_3 (m.d 0 3) (by simp) with h25783 | h25783
                    · linarith only [h20408, h25783, hlam]
                    · rcases p25766_3 (m.d 0 4) (by simp) with h25785 | h25785
                      · linarith only [h20409, h25785, hlam]
                      · linarith only [h20411, h25785, hlam]
                  · linarith only [h20408, h25782, hlam]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h0, h25076, h25287, h25291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                rcases p25766_3 (m.d 0 1) (by simp) with h25790 | h25790
                · linarith only [h0, h25790, hlam]
                · rcases p25766_3 (m.d 0 2) (by simp) with h25792 | h25792
                  · rcases p25766_3 (m.d 0 3) (by simp) with h25793 | h25793
                    · linarith only [h20408, h25793, hlam]
                    · rcases p25766_3 (m.d 0 4) (by simp) with h25795 | h25795
                      · linarith only [h20409, h25795, hlam]
                      · linarith only [h25076, h25795, hlam]
                  · linarith only [h20410, h25792, hlam]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h14396, h25284, h25765, hc01, hc34, hlam, hphi, ht12, ht23, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h20408, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [hlam, p25766_0]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h20411, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h24656, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                rcases p25766_3 (m.d 0 1) (by simp) with h25804 | h25804
                · linarith only [h16915, h25804, hlam]
                · rcases p25766_3 (m.d 0 2) (by simp) with h25806 | h25806
                  · rcases p25766_3 (m.d 0 3) (by simp) with h25807 | h25807
                    · linarith only [h20411, h25807, hlam]
                    · linarith only [h14396, h25807, hlam]
                  · linarith only [h0, h25806, hlam]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h20409, hlam, p25766_0]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                rcases p25766_3 (m.d 0 1) (by simp) with h25812 | h25812
                · linarith only [h16915, h25812, hlam]
                · rcases p25766_3 (m.d 0 2) (by simp) with h25814 | h25814
                  · rcases p25766_3 (m.d 0 3) (by simp) with h25815 | h25815
                    · linarith only [h20411, h25815, hlam]
                    · rcases p25766_3 (m.d 0 4) (by simp) with h25817 | h25817
                      · rcases p25766_3 (m.d 0 5) (by simp) with h25818 | h25818
                        · linarith only [h25076, h25818, hlam]
                        · linarith only [h24656, h25818, hlam]
                      · linarith only [h20411, h25817, hlam]
                  · linarith only [h20408, h25814, hlam]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [hlam, p25766_0]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h16915, h25076, h25080, h25287, h25291, hc23, hc34, hlam, hphi, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                rcases p25766_3 (m.d 0 1) (by simp) with h25825 | h25825
                · linarith only [h18815, h25825, hlam]
                · rcases p25766_3 (m.d 0 2) (by simp) with h25827 | h25827
                  · rcases p25766_3 (m.d 0 3) (by simp) with h25828 | h25828
                    · linarith only [h24656, h25828, hlam]
                    · linarith only [h14396, h25828, hlam]
                  · linarith only [h0, h25827, hlam]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h20410, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                rcases p25766_3 (m.d 0 1) (by simp) with h25833 | h25833
                · linarith only [h18815, h25833, hlam]
                · rcases p25766_3 (m.d 0 2) (by simp) with h25835 | h25835
                  · rcases p25766_3 (m.d 0 3) (by simp) with h25836 | h25836
                    · linarith only [h24656, h25836, hlam]
                    · rcases p25766_3 (m.d 0 4) (by simp) with h25838 | h25838
                      · rcases p25766_3 (m.d 0 5) (by simp) with h25839 | h25839
                        · rcases h2bigk with h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c | h25840c
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h0, hlam, p25840_1]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            rcases p25840_3 (m.d 0 2) (by simp) with h25843 | h25843
                            · rcases p25840_3 (m.d 1 2) (by simp) with h25844 | h25844
                              · rcases p25840_3 (m.d 2 3) (by simp) with h25845 | h25845
                                · linarith only [h25845, hlam, p25840_0]
                                · rcases p25840_3 (m.d 2 4) (by simp) with h25847 | h25847
                                  · linarith only [h20409, h25847, hlam]
                                  · linarith only [h25287, h25847, hlam]
                              · linarith only [h25077, h25844, hlam]
                            · linarith only [h25843, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            rcases p25840_3 (m.d 0 2) (by simp) with h25852 | h25852
                            · rcases p25840_3 (m.d 1 2) (by simp) with h25853 | h25853
                              · rcases p25840_3 (m.d 2 3) (by simp) with h25854 | h25854
                                · linarith only [h20408, h25854, hlam]
                                · rcases p25840_3 (m.d 2 4) (by simp) with h25856 | h25856
                                  · linarith only [h25856, hlam, p25840_0]
                                  · rcases p25840_3 (m.d 2 5) (by simp) with h25858 | h25858
                                    · linarith only [h20410, h25858, hlam]
                                    · linarith only [h25291, h25858, hlam]
                              · linarith only [h25078, h25853, hlam]
                            · linarith only [h25852, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            rcases p25840_3 (m.d 0 2) (by simp) with h25863 | h25863
                            · rcases p25840_3 (m.d 1 2) (by simp) with h25864 | h25864
                              · rcases p25840_3 (m.d 2 3) (by simp) with h25865 | h25865
                                · linarith only [h20408, h25865, hlam]
                                · rcases p25840_3 (m.d 2 4) (by simp) with h25867 | h25867
                                  · linarith only [h20409, h25867, hlam]
                                  · rcases p25840_3 (m.d 2 5) (by simp) with h25869 | h25869
                                    · linarith only [h25869, hlam, p25840_0]
                                    · rcases h3bigk with h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c | h25871c
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h14396, hlam, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25766_1, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h20411, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h24656, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25284, h25765, hc03, hc34, hlam, hphi, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25284, h25765, hc23, hc34, hlam, hphi, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25080, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25284, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h20408, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25077, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25287, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25289, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h14396, hc01, hc34, hlam, hphi, ht12, ht23, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hc13, hc34, hlam, hphi, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hc23, hc34, hlam, hphi, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h14396, h24656, hc01, hc34, hlam, hphi, ht12, ht23, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h14396, hc01, hc35, hlam, hphi, ht12, ht23, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hc23, hc35, hlam, hphi, p25871_1]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [h25765, hlam, p25871_0]
                                      · have p25871_0 := h25871c.1
                                        have p25871_1 := h25871c.2.1
                                        have p25871_2 := h25871c.2.2.1
                                        have p25871_3 := h25871c.2.2.2
                                        linarith only [hlam, p25871_0]
                              · linarith only [h25079, h25864, hlam]
                            · linarith only [h25863, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h14396, h20410, hc01, hc12, hlam, hphi, p25766_1, p25840_1]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            rcases p25840_3 (m.d 0 2) (by simp) with h25901 | h25901
                            · linarith only [h0, h25901, hlam]
                            · linarith only [h20408, h25901, hlam]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            rcases p25840_3 (m.d 0 2) (by simp) with h25904 | h25904
                            · linarith only [h0, h25904, hlam]
                            · linarith only [h20409, h25904, hlam]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            rcases p25840_3 (m.d 0 2) (by simp) with h25907 | h25907
                            · linarith only [h0, h25907, hlam]
                            · linarith only [h20410, h25907, hlam]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h20408, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h25077, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h25287, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h25289, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h20409, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h25078, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h25291, hc23, hc45, hlam, hphi, ht34, p25840_1]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h25291, hlam, p25840_1]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h20410, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h25079, hlam, p25840_0]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h16915, h25076, h25080, h25291, hc23, hc34, hlam, hphi, p25840_1]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [h16915, h25076, h25080, h25287, h25291, hc23, hc34, hlam, hphi, p25840_1]
                          · have p25840_0 := h25840c.1
                            have p25840_1 := h25840c.2.1
                            have p25840_2 := h25840c.2.2.1
                            have p25840_3 := h25840c.2.2.2
                            linarith only [hlam, p25840_0]
                        · linarith only [h24656, h25839, hlam]
                      · linarith only [h20411, h25838, hlam]
                  · linarith only [h20408, h25835, hlam]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [h25076, hlam, p25766_1]
              · have p25766_0 := h25766c.1
                have p25766_1 := h25766c.2.1
                have p25766_2 := h25766c.2.2.1
                have p25766_3 := h25766c.2.2.2
                linarith only [hlam, p25766_0]
            · linarith only [h16915, h25076, h25080, h25765, hlam]
    · linarith only [h16915, h25076, h25286, hlam]

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25078 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25079 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 1 3 4 (by decide) (by decide) with h25080 | h25080
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077 h25078 h25079 h25080
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077 h25078 h25079 h25080

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25078 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25079 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  linarith only [h0, h20410, h25079, hlam]

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25078 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 1 2 5 (by decide) (by decide) with h25079 | h25079
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077 h25078 h25079
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077 h25078 h25079

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25078 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  linarith only [h0, h20409, h25078, hlam]

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 1 2 4 (by decide) (by decide) with h25078 | h25078
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077 h25078
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077 h25078

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h25077 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  linarith only [h0, h20408, h25077, hlam]

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h24656 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h25076 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  rcases m.htr 1 2 3 (by decide) (by decide) with h25077 | h25077
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077
  · exact r1l7_10_12_23_L_I_L_I_H_I_s21_x1_x1_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 h20411 h24656 h25076 h25077

end R2N4
