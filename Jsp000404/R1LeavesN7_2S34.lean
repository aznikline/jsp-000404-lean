import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
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
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h22733 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h22734 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23282 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 2 3 5 (by decide) (by decide) with h23283 | h23283
  · rcases m.htr 2 4 5 (by decide) (by decide) with h23284 | h23284
    · linarith only [h16915, h22734, h23284, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h23286 | h23286
      · linarith only [h16915, h20409, h22734, h23282, h23286, hlam]
      · rcases h0bigk with h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c | h23288c
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h0, hlam, p23288_1]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h14396, hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h16915, hlam, p23288_1]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h18815, hlam, p23288_1]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23294 | h23294
          · linarith only [h0, h23294, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23296 | h23296
            · rcases p23288_3 (m.d 0 3) (by simp) with h23297 | h23297
              · linarith only [h20408, h23297, hlam]
              · linarith only [h14396, h23297, hlam]
            · linarith only [h0, h23296, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23302 | h23302
          · linarith only [h0, h23302, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23304 | h23304
            · rcases p23288_3 (m.d 0 3) (by simp) with h23305 | h23305
              · linarith only [h20408, h23305, hlam]
              · rcases p23288_3 (m.d 0 4) (by simp) with h23307 | h23307
                · linarith only [h20409, h23307, hlam]
                · rcases p23288_3 (m.d 0 5) (by simp) with h23309 | h23309
                  · linarith only [h20410, h23309, hlam]
                  · rcases h2bigk with h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c | h23311c
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h0, hlam, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      rcases p23311_3 (m.d 0 2) (by simp) with h23314 | h23314
                      · rcases p23311_3 (m.d 1 2) (by simp) with h23315 | h23315
                        · rcases p23311_3 (m.d 2 3) (by simp) with h23316 | h23316
                          · linarith only [h23316, hlam, p23311_0]
                          · rcases p23311_3 (m.d 2 4) (by simp) with h23318 | h23318
                            · linarith only [h20409, h23318, hlam]
                            · rcases p23311_3 (m.d 2 5) (by simp) with h23320 | h23320
                              · linarith only [h20410, h23320, hlam]
                              · rcases h3bigk with h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c | h23322c
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h14396, hlam, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h0, h23283, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23288_1, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23288_1, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h0, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23288_1, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h22729, h23283, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  rcases p23322_3 (m.d 0 3) (by simp) with h23331 | h23331
                                  · linarith only [h14396, h23331, hlam]
                                  · linarith only [h20411, h23331, hlam]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  rcases p23322_3 (m.d 0 3) (by simp) with h23334 | h23334
                                  · linarith only [h14396, h23334, hlam]
                                  · linarith only [h20412, h23334, hlam]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h20408, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h22729, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23311_1, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h0, h20408, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23288_1, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h20411, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h22732, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h23282, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h23286, hlam, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h20412, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h22733, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h23283, hlam, p23322_0]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [h0, h20412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23288_1, p23322_1]
                                · have p23322_0 := h23322c.1
                                  have p23322_1 := h23322c.2.1
                                  have p23322_2 := h23322c.2.2.1
                                  have p23322_3 := h23322c.2.2.2
                                  linarith only [hlam, p23322_0]
                        · linarith only [h22729, h23315, hlam]
                      · linarith only [h23314, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      rcases p23311_3 (m.d 0 2) (by simp) with h23354 | h23354
                      · rcases p23311_3 (m.d 1 2) (by simp) with h23355 | h23355
                        · rcases p23311_3 (m.d 2 3) (by simp) with h23356 | h23356
                          · linarith only [h20408, h23356, hlam]
                          · linarith only [h23282, h23356, hlam]
                        · linarith only [h22730, h23355, hlam]
                      · linarith only [h23354, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      rcases p23311_3 (m.d 0 2) (by simp) with h23361 | h23361
                      · rcases p23311_3 (m.d 1 2) (by simp) with h23362 | h23362
                        · rcases p23311_3 (m.d 2 3) (by simp) with h23363 | h23363
                          · linarith only [h20408, h23363, hlam]
                          · linarith only [h23283, h23363, hlam]
                        · linarith only [h22731, h23362, hlam]
                      · linarith only [h23361, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23288_1, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      rcases p23311_3 (m.d 0 2) (by simp) with h23370 | h23370
                      · linarith only [h0, h23370, hlam]
                      · linarith only [h20408, h23370, hlam]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      rcases p23311_3 (m.d 0 2) (by simp) with h23373 | h23373
                      · linarith only [h0, h23373, hlam]
                      · linarith only [h20409, h23373, hlam]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      rcases p23311_3 (m.d 0 2) (by simp) with h23376 | h23376
                      · linarith only [h0, h23376, hlam]
                      · linarith only [h20410, h23376, hlam]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h20408, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h22729, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h20408, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p23288_1, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h20408, hc02, hc25, hlam, hphi, ht0b, ht5b, p23288_1, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h20409, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h22730, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h23282, hlam, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h23284, hlam, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h20410, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h22731, hlam, p23311_0]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h23283, hlam, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [h0, h20410, h20412, h23282, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23288_1, p23311_1]
                    · have p23311_0 := h23311c.1
                      have p23311_1 := h23311c.2.1
                      have p23311_2 := h23311c.2.2.1
                      have p23311_3 := h23311c.2.2.2
                      linarith only [hlam, p23311_0]
            · linarith only [h20408, h23304, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23395 | h23395
          · linarith only [h0, h23395, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23397 | h23397
            · rcases p23288_3 (m.d 0 3) (by simp) with h23398 | h23398
              · linarith only [h20408, h23398, hlam]
              · linarith only [h20411, h23398, hlam]
            · linarith only [h20409, h23397, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23402 | h23402
          · linarith only [h0, h23402, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23404 | h23404
            · rcases p23288_3 (m.d 0 3) (by simp) with h23405 | h23405
              · linarith only [h20408, h23405, hlam]
              · linarith only [h20412, h23405, hlam]
            · linarith only [h20410, h23404, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23409 | h23409
          · linarith only [h14396, h23409, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23411 | h23411
            · rcases p23288_3 (m.d 0 3) (by simp) with h23412 | h23412
              · rcases p23288_3 (m.d 0 4) (by simp) with h23413 | h23413
                · linarith only [h20411, h23413, hlam]
                · linarith only [h16915, h23413, hlam]
              · linarith only [h14396, h23412, hlam]
            · linarith only [h0, h23411, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h20408, hlam, p23288_1]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23420 | h23420
          · linarith only [h14396, h23420, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23422 | h23422
            · rcases p23288_3 (m.d 0 3) (by simp) with h23423 | h23423
              · rcases p23288_3 (m.d 0 4) (by simp) with h23424 | h23424
                · linarith only [h20411, h23424, hlam]
                · rcases p23288_3 (m.d 0 5) (by simp) with h23426 | h23426
                  · linarith only [h20412, h23426, hlam]
                  · linarith only [h20413, h23426, hlam]
              · linarith only [h20411, h23423, hlam]
            · linarith only [h20409, h23422, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23431 | h23431
          · linarith only [h14396, h23431, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23433 | h23433
            · rcases p23288_3 (m.d 0 3) (by simp) with h23434 | h23434
              · rcases p23288_3 (m.d 0 4) (by simp) with h23435 | h23435
                · linarith only [h20411, h23435, hlam]
                · rcases p23288_3 (m.d 0 5) (by simp) with h23437 | h23437
                  · linarith only [h20412, h23437, hlam]
                  · rcases h2bigk with h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c | h23439c
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h0, hlam, p23439_1]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23442 | h23442
                      · rcases p23439_3 (m.d 1 2) (by simp) with h23443 | h23443
                        · rcases p23439_3 (m.d 2 3) (by simp) with h23444 | h23444
                          · linarith only [h23444, hlam, p23439_0]
                          · rcases p23439_3 (m.d 2 4) (by simp) with h23446 | h23446
                            · linarith only [h20409, h23446, hlam]
                            · rcases p23439_3 (m.d 2 5) (by simp) with h23448 | h23448
                              · linarith only [h20410, h23448, hlam]
                              · rcases h3bigk with h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c | h23450c
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h14396, hlam, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h20408, hlam, p23439_2, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  rcases p23450_3 (m.d 0 3) (by simp) with h23454 | h23454
                                  · rcases p23450_3 (m.d 1 3) (by simp) with h23455 | h23455
                                    · rcases p23450_3 (m.d 2 3) (by simp) with h23456 | h23456
                                      · linarith only [h20408, h23456, hlam]
                                      · linarith only [h23282, h23456, hlam]
                                    · linarith only [h22732, h23455, hlam]
                                  · linarith only [h23454, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  rcases p23450_3 (m.d 0 3) (by simp) with h23461 | h23461
                                  · rcases p23450_3 (m.d 1 3) (by simp) with h23462 | h23462
                                    · rcases p23450_3 (m.d 2 3) (by simp) with h23463 | h23463
                                      · linarith only [h20408, h23463, hlam]
                                      · linarith only [h23283, h23463, hlam]
                                    · linarith only [h22733, h23462, hlam]
                                  · linarith only [h23461, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h22729, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p23288_1, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h22729, h23282, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  rcases p23450_3 (m.d 0 3) (by simp) with h23471 | h23471
                                  · linarith only [h14396, h23471, hlam]
                                  · linarith only [h20411, h23471, hlam]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  rcases p23450_3 (m.d 0 3) (by simp) with h23474 | h23474
                                  · linarith only [h14396, h23474, hlam]
                                  · linarith only [h20412, h23474, hlam]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h20408, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h22729, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23439_1, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h0, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23439_1, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h20411, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h22732, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h23282, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h23286, hlam, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h20412, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h22733, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h23283, hlam, p23450_0]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [h0, h20410, h23283, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23450_1]
                                · have p23450_0 := h23450c.1
                                  have p23450_1 := h23450c.2.1
                                  have p23450_2 := h23450c.2.2.1
                                  have p23450_3 := h23450c.2.2.2
                                  linarith only [hlam, p23450_0]
                        · linarith only [h22729, h23443, hlam]
                      · linarith only [h23442, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23494 | h23494
                      · rcases p23439_3 (m.d 1 2) (by simp) with h23495 | h23495
                        · rcases p23439_3 (m.d 2 3) (by simp) with h23496 | h23496
                          · linarith only [h20408, h23496, hlam]
                          · linarith only [h23282, h23496, hlam]
                        · linarith only [h22730, h23495, hlam]
                      · linarith only [h23494, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23501 | h23501
                      · rcases p23439_3 (m.d 1 2) (by simp) with h23502 | h23502
                        · rcases p23439_3 (m.d 2 3) (by simp) with h23503 | h23503
                          · linarith only [h20408, h23503, hlam]
                          · linarith only [h23283, h23503, hlam]
                        · linarith only [h22731, h23502, hlam]
                      · linarith only [h23501, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h20408, h23283, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23439_1]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23510 | h23510
                      · linarith only [h0, h23510, hlam]
                      · linarith only [h20408, h23510, hlam]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23513 | h23513
                      · linarith only [h0, h23513, hlam]
                      · linarith only [h20409, h23513, hlam]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23516 | h23516
                      · linarith only [h0, h23516, hlam]
                      · linarith only [h20410, h23516, hlam]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h20408, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h22729, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23522 | h23522
                      · rcases p23439_3 (m.d 1 2) (by simp) with h23523 | h23523
                        · rcases p23439_3 (m.d 2 3) (by simp) with h23524 | h23524
                          · rcases p23439_3 (m.d 2 4) (by simp) with h23525 | h23525
                            · linarith only [h23282, h23525, hlam]
                            · rcases p23439_3 (m.d 2 5) (by simp) with h23527 | h23527
                              · linarith only [h23283, h23527, hlam]
                              · linarith only [h23284, h23527, hlam]
                          · linarith only [h23282, h23524, hlam]
                        · linarith only [h22730, h23523, hlam]
                      · linarith only [h20409, h23522, hlam]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      rcases p23439_3 (m.d 0 2) (by simp) with h23533 | h23533
                      · rcases p23439_3 (m.d 1 2) (by simp) with h23534 | h23534
                        · rcases p23439_3 (m.d 2 3) (by simp) with h23535 | h23535
                          · rcases p23439_3 (m.d 2 4) (by simp) with h23536 | h23536
                            · linarith only [h23282, h23536, hlam]
                            · rcases p23439_3 (m.d 2 5) (by simp) with h23538 | h23538
                              · linarith only [h23283, h23538, hlam]
                              · rcases h3bigk with h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c | h23540c
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h14396, hlam, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h23283, h23286, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23439_1, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  rcases p23540_3 (m.d 0 3) (by simp) with h23544 | h23544
                                  · rcases p23540_3 (m.d 1 3) (by simp) with h23545 | h23545
                                    · rcases p23540_3 (m.d 2 3) (by simp) with h23546 | h23546
                                      · linarith only [h20408, h23546, hlam]
                                      · linarith only [h23282, h23546, hlam]
                                    · linarith only [h22732, h23545, hlam]
                                  · linarith only [h23544, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  rcases p23540_3 (m.d 0 3) (by simp) with h23551 | h23551
                                  · rcases p23540_3 (m.d 1 3) (by simp) with h23552 | h23552
                                    · rcases p23540_3 (m.d 2 3) (by simp) with h23553 | h23553
                                      · linarith only [h20408, h23553, hlam]
                                      · linarith only [h23283, h23553, hlam]
                                    · linarith only [h22733, h23552, hlam]
                                  · linarith only [h23551, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h22729, h23283, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23439_1, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  rcases p23540_3 (m.d 0 3) (by simp) with h23561 | h23561
                                  · linarith only [h14396, h23561, hlam]
                                  · linarith only [h20411, h23561, hlam]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  rcases p23540_3 (m.d 0 3) (by simp) with h23564 | h23564
                                  · linarith only [h14396, h23564, hlam]
                                  · linarith only [h20412, h23564, hlam]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h20408, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h22729, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h20408, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h0, h20408, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h20411, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h22732, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h23282, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h23286, hlam, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h20412, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h22733, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h23283, hlam, p23540_0]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [h0, h20410, h23283, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23540_1]
                                · have p23540_0 := h23540c.1
                                  have p23540_1 := h23540c.2.1
                                  have p23540_2 := h23540c.2.2.1
                                  have p23540_3 := h23540c.2.2.2
                                  linarith only [hlam, p23540_0]
                          · linarith only [h23283, h23535, hlam]
                        · linarith only [h22731, h23534, hlam]
                      · linarith only [h20410, h23533, hlam]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h20409, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h22730, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h23282, hlam, p23439_1]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h23284, hlam, p23439_1]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h20410, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h22731, hlam, p23439_0]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h23283, hlam, p23439_1]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [h20410, h23282, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23288_1, p23439_1]
                    · have p23439_0 := h23439c.1
                      have p23439_1 := h23439c.2.1
                      have p23439_2 := h23439c.2.2.1
                      have p23439_3 := h23439c.2.2.2
                      linarith only [hlam, p23439_0]
              · linarith only [h20412, h23434, hlam]
            · linarith only [h20410, h23433, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h16915, h22734, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p23288_1]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h20409, hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h20411, hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h20413, hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23602 | h23602
          · linarith only [h18815, h23602, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23604 | h23604
            · rcases p23288_3 (m.d 0 3) (by simp) with h23605 | h23605
              · rcases p23288_3 (m.d 0 4) (by simp) with h23606 | h23606
                · linarith only [h20413, h23606, hlam]
                · linarith only [h16915, h23606, hlam]
              · linarith only [h14396, h23605, hlam]
            · linarith only [h0, h23604, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h20410, hlam, p23288_1]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [h20412, hlam, p23288_0]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          rcases p23288_3 (m.d 0 1) (by simp) with h23613 | h23613
          · linarith only [h18815, h23613, hlam]
          · rcases p23288_3 (m.d 0 2) (by simp) with h23615 | h23615
            · rcases p23288_3 (m.d 0 3) (by simp) with h23616 | h23616
              · rcases p23288_3 (m.d 0 4) (by simp) with h23617 | h23617
                · linarith only [h20413, h23617, hlam]
                · rcases p23288_3 (m.d 0 5) (by simp) with h23619 | h23619
                  · rcases h2bigk with h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c | h23620c
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h0, hlam, p23620_1]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23623 | h23623
                      · rcases p23620_3 (m.d 1 2) (by simp) with h23624 | h23624
                        · rcases p23620_3 (m.d 2 3) (by simp) with h23625 | h23625
                          · linarith only [h23625, hlam, p23620_0]
                          · rcases p23620_3 (m.d 2 4) (by simp) with h23627 | h23627
                            · linarith only [h20409, h23627, hlam]
                            · rcases p23620_3 (m.d 2 5) (by simp) with h23629 | h23629
                              · linarith only [h20410, h23629, hlam]
                              · rcases h3bigk with h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c | h23631c
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h14396, hlam, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h14396, h22729, h23283, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  rcases p23631_3 (m.d 0 3) (by simp) with h23635 | h23635
                                  · rcases p23631_3 (m.d 1 3) (by simp) with h23636 | h23636
                                    · rcases p23631_3 (m.d 2 3) (by simp) with h23637 | h23637
                                      · linarith only [h20408, h23637, hlam]
                                      · linarith only [h23282, h23637, hlam]
                                    · linarith only [h22732, h23636, hlam]
                                  · linarith only [h23635, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  rcases p23631_3 (m.d 0 3) (by simp) with h23642 | h23642
                                  · rcases p23631_3 (m.d 1 3) (by simp) with h23643 | h23643
                                    · rcases p23631_3 (m.d 2 3) (by simp) with h23644 | h23644
                                      · linarith only [h20408, h23644, hlam]
                                      · linarith only [h23283, h23644, hlam]
                                    · linarith only [h22733, h23643, hlam]
                                  · linarith only [h23642, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h22729, h23283, h23286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  rcases p23631_3 (m.d 0 3) (by simp) with h23652 | h23652
                                  · linarith only [h14396, h23652, hlam]
                                  · linarith only [h20411, h23652, hlam]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  rcases p23631_3 (m.d 0 3) (by simp) with h23655 | h23655
                                  · linarith only [h14396, h23655, hlam]
                                  · linarith only [h20412, h23655, hlam]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h20408, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h22729, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h0, h16915, h18815, h22734, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23620_1, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h0, h16915, h18815, h22734, h23286, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23620_1, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h20411, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h22732, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h23282, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h23286, hlam, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h20412, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h22733, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h23283, hlam, p23631_0]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23631_1]
                                · have p23631_0 := h23631c.1
                                  have p23631_1 := h23631c.2.1
                                  have p23631_2 := h23631c.2.2.1
                                  have p23631_3 := h23631c.2.2.2
                                  linarith only [hlam, p23631_0]
                        · linarith only [h22729, h23624, hlam]
                      · linarith only [h23623, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23675 | h23675
                      · rcases p23620_3 (m.d 1 2) (by simp) with h23676 | h23676
                        · rcases p23620_3 (m.d 2 3) (by simp) with h23677 | h23677
                          · linarith only [h20408, h23677, hlam]
                          · linarith only [h23282, h23677, hlam]
                        · linarith only [h22730, h23676, hlam]
                      · linarith only [h23675, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23682 | h23682
                      · rcases p23620_3 (m.d 1 2) (by simp) with h23683 | h23683
                        · rcases p23620_3 (m.d 2 3) (by simp) with h23684 | h23684
                          · linarith only [h20408, h23684, hlam]
                          · linarith only [h23283, h23684, hlam]
                        · linarith only [h22731, h23683, hlam]
                      · linarith only [h23682, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h20408, h23283, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23620_1]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23691 | h23691
                      · linarith only [h0, h23691, hlam]
                      · linarith only [h20408, h23691, hlam]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23694 | h23694
                      · linarith only [h0, h23694, hlam]
                      · linarith only [h20409, h23694, hlam]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23697 | h23697
                      · linarith only [h0, h23697, hlam]
                      · linarith only [h20410, h23697, hlam]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h20408, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h22729, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23703 | h23703
                      · rcases p23620_3 (m.d 1 2) (by simp) with h23704 | h23704
                        · rcases p23620_3 (m.d 2 3) (by simp) with h23705 | h23705
                          · rcases p23620_3 (m.d 2 4) (by simp) with h23706 | h23706
                            · linarith only [h23282, h23706, hlam]
                            · rcases p23620_3 (m.d 2 5) (by simp) with h23708 | h23708
                              · linarith only [h23283, h23708, hlam]
                              · linarith only [h23284, h23708, hlam]
                          · linarith only [h23282, h23705, hlam]
                        · linarith only [h22730, h23704, hlam]
                      · linarith only [h20409, h23703, hlam]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23714 | h23714
                      · rcases p23620_3 (m.d 1 2) (by simp) with h23715 | h23715
                        · rcases p23620_3 (m.d 2 3) (by simp) with h23716 | h23716
                          · rcases p23620_3 (m.d 2 4) (by simp) with h23717 | h23717
                            · linarith only [h23282, h23717, hlam]
                            · rcases p23620_3 (m.d 2 5) (by simp) with h23719 | h23719
                              · linarith only [h23283, h23719, hlam]
                              · rcases h3bigk with h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c | h23721c
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h14396, hlam, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h23283, h23286, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23620_1, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  rcases p23721_3 (m.d 0 3) (by simp) with h23725 | h23725
                                  · rcases p23721_3 (m.d 1 3) (by simp) with h23726 | h23726
                                    · rcases p23721_3 (m.d 2 3) (by simp) with h23727 | h23727
                                      · linarith only [h20408, h23727, hlam]
                                      · linarith only [h23282, h23727, hlam]
                                    · linarith only [h22732, h23726, hlam]
                                  · linarith only [h23725, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  rcases p23721_3 (m.d 0 3) (by simp) with h23732 | h23732
                                  · rcases p23721_3 (m.d 1 3) (by simp) with h23733 | h23733
                                    · rcases p23721_3 (m.d 2 3) (by simp) with h23734 | h23734
                                      · linarith only [h20408, h23734, hlam]
                                      · linarith only [h23283, h23734, hlam]
                                    · linarith only [h22733, h23733, hlam]
                                  · linarith only [h23732, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h16915, h18815, h22729, h22734, h23283, h23286, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23620_1, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  rcases p23721_3 (m.d 0 3) (by simp) with h23742 | h23742
                                  · linarith only [h14396, h23742, hlam]
                                  · linarith only [h20411, h23742, hlam]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  rcases p23721_3 (m.d 0 3) (by simp) with h23745 | h23745
                                  · linarith only [h14396, h23745, hlam]
                                  · linarith only [h20412, h23745, hlam]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h20408, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h22729, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h20408, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h0, h16915, h18815, h20408, h22734, h23286, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h20411, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h22732, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h23282, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h23286, hlam, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h20412, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h22733, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h23283, hlam, p23721_0]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [h0, h16915, h18815, h20410, h22734, h23283, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23721_1]
                                · have p23721_0 := h23721c.1
                                  have p23721_1 := h23721c.2.1
                                  have p23721_2 := h23721c.2.2.1
                                  have p23721_3 := h23721c.2.2.2
                                  linarith only [hlam, p23721_0]
                          · linarith only [h23283, h23716, hlam]
                        · linarith only [h22731, h23715, hlam]
                      · linarith only [h20410, h23714, hlam]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h20409, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h22730, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h23282, hlam, p23620_1]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h23284, hlam, p23620_1]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h20410, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h22731, hlam, p23620_0]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [h23283, hlam, p23620_1]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      rcases p23620_3 (m.d 0 2) (by simp) with h23774 | h23774
                      · rcases p23620_3 (m.d 1 2) (by simp) with h23775 | h23775
                        · rcases p23620_3 (m.d 2 3) (by simp) with h23776 | h23776
                          · rcases p23620_3 (m.d 2 4) (by simp) with h23777 | h23777
                            · linarith only [h23284, h23777, hlam]
                            · rcases p23620_3 (m.d 2 5) (by simp) with h23779 | h23779
                              · rcases h3bigk with h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c | h23780c
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h14396, hlam, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h23283, hc03, hc35, hlam, hphi, ht0b, ht5b, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  rcases p23780_3 (m.d 0 3) (by simp) with h23784 | h23784
                                  · rcases p23780_3 (m.d 1 3) (by simp) with h23785 | h23785
                                    · rcases p23780_3 (m.d 2 3) (by simp) with h23786 | h23786
                                      · linarith only [h20408, h23786, hlam]
                                      · linarith only [h23282, h23786, hlam]
                                    · linarith only [h22732, h23785, hlam]
                                  · linarith only [h23784, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  rcases p23780_3 (m.d 0 3) (by simp) with h23791 | h23791
                                  · rcases p23780_3 (m.d 1 3) (by simp) with h23792 | h23792
                                    · rcases p23780_3 (m.d 2 3) (by simp) with h23793 | h23793
                                      · linarith only [h20408, h23793, hlam]
                                      · linarith only [h23283, h23793, hlam]
                                    · linarith only [h22733, h23792, hlam]
                                  · linarith only [h23791, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h16915, h18815, h22729, h22734, h23282, h23283, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23620_1, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  rcases p23780_3 (m.d 0 3) (by simp) with h23801 | h23801
                                  · linarith only [h14396, h23801, hlam]
                                  · linarith only [h20411, h23801, hlam]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  rcases p23780_3 (m.d 0 3) (by simp) with h23804 | h23804
                                  · linarith only [h14396, h23804, hlam]
                                  · linarith only [h20412, h23804, hlam]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h20408, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h22729, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h0, h16915, h18815, h20408, h22734, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h0, h16915, h18815, h20408, h22734, h23286, hc01, hc12, hc34, hc45, hlam, hphi, p23288_1, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h20411, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h22732, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h23282, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h23286, hlam, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h20412, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h22733, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h23283, hlam, p23780_0]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [h20412, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23780_1]
                                · have p23780_0 := h23780c.1
                                  have p23780_1 := h23780c.2.1
                                  have p23780_2 := h23780c.2.2.1
                                  have p23780_3 := h23780c.2.2.2
                                  linarith only [hlam, p23780_0]
                              · linarith only [h23284, h23779, hlam]
                          · linarith only [h23282, h23776, hlam]
                        · linarith only [h22730, h23775, hlam]
                      · linarith only [h20409, h23774, hlam]
                    · have p23620_0 := h23620c.1
                      have p23620_1 := h23620c.2.1
                      have p23620_2 := h23620c.2.2.1
                      have p23620_3 := h23620c.2.2.2
                      linarith only [hlam, p23620_0]
                  · linarith only [h20413, h23619, hlam]
              · linarith only [h20411, h23616, hlam]
            · linarith only [h20409, h23615, hlam]
        · have p23288_0 := h23288c.1
          have p23288_1 := h23288c.2.1
          have p23288_2 := h23288c.2.2.1
          have p23288_3 := h23288c.2.2.2
          linarith only [hlam, p23288_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h23831 | h23831
    · linarith only [h16915, h22734, h23831, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h23833 | h23833
      · linarith only [h16915, h20412, h22734, h23282, h23283, h23833, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
      · rcases h0bigk with h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c | h23835c
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h0, hlam, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h14396, hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h16915, hlam, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h18815, hlam, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          rcases p23835_3 (m.d 0 1) (by simp) with h23841 | h23841
          · linarith only [h0, h23841, hlam]
          · rcases p23835_3 (m.d 0 2) (by simp) with h23843 | h23843
            · rcases p23835_3 (m.d 0 3) (by simp) with h23844 | h23844
              · linarith only [h20408, h23844, hlam]
              · linarith only [h14396, h23844, hlam]
            · linarith only [h0, h23843, hlam]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h0, h20412, h23283, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          rcases p23835_3 (m.d 0 1) (by simp) with h23850 | h23850
          · linarith only [h0, h23850, hlam]
          · rcases p23835_3 (m.d 0 2) (by simp) with h23852 | h23852
            · rcases p23835_3 (m.d 0 3) (by simp) with h23853 | h23853
              · linarith only [h20408, h23853, hlam]
              · linarith only [h20411, h23853, hlam]
            · linarith only [h20409, h23852, hlam]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h0, h20412, h23282, h23283, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          rcases p23835_3 (m.d 0 1) (by simp) with h23858 | h23858
          · linarith only [h14396, h23858, hlam]
          · rcases p23835_3 (m.d 0 2) (by simp) with h23860 | h23860
            · rcases p23835_3 (m.d 0 3) (by simp) with h23861 | h23861
              · rcases p23835_3 (m.d 0 4) (by simp) with h23862 | h23862
                · linarith only [h20411, h23862, hlam]
                · linarith only [h16915, h23862, hlam]
              · linarith only [h14396, h23861, hlam]
            · linarith only [h0, h23860, hlam]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h20408, hlam, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          rcases p23835_3 (m.d 0 1) (by simp) with h23869 | h23869
          · linarith only [h14396, h23869, hlam]
          · rcases p23835_3 (m.d 0 2) (by simp) with h23871 | h23871
            · rcases p23835_3 (m.d 0 3) (by simp) with h23872 | h23872
              · rcases p23835_3 (m.d 0 4) (by simp) with h23873 | h23873
                · linarith only [h20411, h23873, hlam]
                · rcases p23835_3 (m.d 0 5) (by simp) with h23875 | h23875
                  · linarith only [h20412, h23875, hlam]
                  · linarith only [h20413, h23875, hlam]
              · linarith only [h20411, h23872, hlam]
            · linarith only [h20409, h23871, hlam]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h20412, h23282, h23283, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h16915, h22734, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h20409, hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h20411, hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h20413, hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          rcases p23835_3 (m.d 0 1) (by simp) with h23886 | h23886
          · linarith only [h18815, h23886, hlam]
          · rcases p23835_3 (m.d 0 2) (by simp) with h23888 | h23888
            · rcases p23835_3 (m.d 0 3) (by simp) with h23889 | h23889
              · rcases p23835_3 (m.d 0 4) (by simp) with h23890 | h23890
                · linarith only [h20413, h23890, hlam]
                · linarith only [h16915, h23890, hlam]
              · linarith only [h14396, h23889, hlam]
            · linarith only [h0, h23888, hlam]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h20410, hlam, p23835_1]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [h20412, hlam, p23835_0]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          rcases p23835_3 (m.d 0 1) (by simp) with h23897 | h23897
          · linarith only [h18815, h23897, hlam]
          · rcases p23835_3 (m.d 0 2) (by simp) with h23899 | h23899
            · rcases p23835_3 (m.d 0 3) (by simp) with h23900 | h23900
              · rcases p23835_3 (m.d 0 4) (by simp) with h23901 | h23901
                · linarith only [h20413, h23901, hlam]
                · rcases p23835_3 (m.d 0 5) (by simp) with h23903 | h23903
                  · rcases h2bigk with h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c | h23904c
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h0, hlam, p23904_1]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      rcases p23904_3 (m.d 0 2) (by simp) with h23907 | h23907
                      · rcases p23904_3 (m.d 1 2) (by simp) with h23908 | h23908
                        · rcases p23904_3 (m.d 2 3) (by simp) with h23909 | h23909
                          · linarith only [h23909, hlam, p23904_0]
                          · rcases p23904_3 (m.d 2 4) (by simp) with h23911 | h23911
                            · linarith only [h20409, h23911, hlam]
                            · rcases p23904_3 (m.d 2 5) (by simp) with h23913 | h23913
                              · linarith only [h20410, h23913, hlam]
                              · linarith only [h23283, h23913, hlam]
                        · linarith only [h22729, h23908, hlam]
                      · linarith only [h23907, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      rcases p23904_3 (m.d 0 2) (by simp) with h23918 | h23918
                      · rcases p23904_3 (m.d 1 2) (by simp) with h23919 | h23919
                        · rcases p23904_3 (m.d 2 3) (by simp) with h23920 | h23920
                          · linarith only [h20408, h23920, hlam]
                          · linarith only [h23282, h23920, hlam]
                        · linarith only [h22730, h23919, hlam]
                      · linarith only [h23918, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      rcases p23904_3 (m.d 0 2) (by simp) with h23925 | h23925
                      · rcases p23904_3 (m.d 1 2) (by simp) with h23926 | h23926
                        · rcases p23904_3 (m.d 2 3) (by simp) with h23927 | h23927
                          · linarith only [h20408, h23927, hlam]
                          · rcases p23904_3 (m.d 2 4) (by simp) with h23929 | h23929
                            · linarith only [h20409, h23929, hlam]
                            · rcases p23904_3 (m.d 2 5) (by simp) with h23931 | h23931
                              · linarith only [h23931, hlam, p23904_0]
                              · rcases h3bigk with h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c | h23933c
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h14396, hlam, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h14396, h22729, h23282, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  rcases p23933_3 (m.d 0 3) (by simp) with h23937 | h23937
                                  · rcases p23933_3 (m.d 1 3) (by simp) with h23938 | h23938
                                    · rcases p23933_3 (m.d 2 3) (by simp) with h23939 | h23939
                                      · linarith only [h20408, h23939, hlam]
                                      · linarith only [h23282, h23939, hlam]
                                    · linarith only [h22732, h23938, hlam]
                                  · linarith only [h23937, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h14396, h16915, h18815, h22729, h22734, h23282, h23283, hc01, hc12, hc34, hc45, hlam, hphi, p23835_1, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h14396, h22729, hc01, hc12, hlam, hphi, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h16915, h18815, h22729, h22734, h23282, hc01, hc12, hc34, hc45, hlam, hphi, p23835_1, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  rcases p23933_3 (m.d 0 3) (by simp) with h23948 | h23948
                                  · linarith only [h14396, h23948, hlam]
                                  · linarith only [h20411, h23948, hlam]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h16915, h18815, h22729, h22734, h23282, h23283, hc01, hc12, hc34, hc45, hlam, hphi, p23835_1, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h20408, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h22729, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h20412, h23283, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h23283, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h20411, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h22732, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h23282, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h23833, hlam, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h20412, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h22733, hlam, p23933_0]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h20412, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [h14396, h16915, h18815, h20412, h22729, h22734, hc01, hc12, hc34, hc45, hlam, hphi, p23835_1, p23933_1]
                                · have p23933_0 := h23933c.1
                                  have p23933_1 := h23933c.2.1
                                  have p23933_2 := h23933c.2.2.1
                                  have p23933_3 := h23933c.2.2.2
                                  linarith only [hlam, p23933_0]
                        · linarith only [h22731, h23926, hlam]
                      · linarith only [h23925, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h16915, h18815, h20408, h22734, h23282, hc01, hc12, hc34, hc45, hlam, hphi, p23835_1, p23904_1]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      rcases p23904_3 (m.d 0 2) (by simp) with h23971 | h23971
                      · linarith only [h0, h23971, hlam]
                      · linarith only [h20408, h23971, hlam]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      rcases p23904_3 (m.d 0 2) (by simp) with h23974 | h23974
                      · linarith only [h0, h23974, hlam]
                      · linarith only [h20409, h23974, hlam]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      rcases p23904_3 (m.d 0 2) (by simp) with h23977 | h23977
                      · linarith only [h0, h23977, hlam]
                      · linarith only [h20410, h23977, hlam]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h20408, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h22729, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h14396, h16915, h18815, h20412, h22729, h22734, h23282, h23283, hc01, hc12, hc34, hc45, hlam, hphi, p23835_1, p23904_1]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h23283, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h20409, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h22730, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h23282, hlam, p23904_1]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h23831, hlam, p23904_1]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h20410, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h22731, hlam, p23904_0]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [h0, h16915, h18815, h20410, h22734, h23282, hc01, hc12, hc34, hc45, hlam, hphi, p23835_1, p23904_1]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      rcases p23904_3 (m.d 0 2) (by simp) with h23993 | h23993
                      · rcases p23904_3 (m.d 1 2) (by simp) with h23994 | h23994
                        · rcases p23904_3 (m.d 2 3) (by simp) with h23995 | h23995
                          · linarith only [h23283, h23995, hlam]
                          · linarith only [h23282, h23995, hlam]
                        · linarith only [h22730, h23994, hlam]
                      · linarith only [h20409, h23993, hlam]
                    · have p23904_0 := h23904c.1
                      have p23904_1 := h23904c.2.1
                      have p23904_2 := h23904c.2.2.1
                      have p23904_3 := h23904c.2.2.2
                      linarith only [hlam, p23904_0]
                  · linarith only [h20413, h23903, hlam]
              · linarith only [h20411, h23900, hlam]
            · linarith only [h20409, h23899, hlam]
        · have p23835_0 := h23835c.1
          have p23835_1 := h23835c.2.1
          have p23835_2 := h23835c.2.2.1
          have p23835_3 := h23835c.2.2.2
          linarith only [hlam, p23835_0]

end R2N4
