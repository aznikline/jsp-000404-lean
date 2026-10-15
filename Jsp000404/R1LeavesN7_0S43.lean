import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26255 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h26256 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h26257 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  rcases m.htr 3 4 5 (by decide) (by decide) with h26258 | h26258
  · linarith only [h0, h19744, h23337, h23339, h26258, h4, hc12, hc23, hlam, hphi]
  · rcases h1bigk with h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c | h26260c
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      rcases p26260_3 (m.d 0 1) (by simp) with h26262 | h26262
      · rcases p26260_3 (m.d 1 2) (by simp) with h26263 | h26263
        · linarith only [h26263, hlam, p26260_0]
        · rcases p26260_3 (m.d 1 3) (by simp) with h26265 | h26265
          · linarith only [h1, h26265, hlam]
          · linarith only [h26245, h26265, hlam]
      · linarith only [h26262, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      rcases p26260_3 (m.d 0 1) (by simp) with h26269 | h26269
      · rcases p26260_3 (m.d 1 2) (by simp) with h26270 | h26270
        · linarith only [h0, h26270, hlam]
        · rcases p26260_3 (m.d 1 3) (by simp) with h26272 | h26272
          · linarith only [h26272, hlam, p26260_0]
          · rcases p26260_3 (m.d 1 4) (by simp) with h26274 | h26274
            · linarith only [h2, h26274, hlam]
            · rcases p26260_3 (m.d 1 5) (by simp) with h26276 | h26276
              · linarith only [h26276, h3, hlam]
              · rcases h1emax with h26278 | h26278 | h26278 | h26278 | h26278
                · linarith only [h26252, h26258, h26278, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p26260_1]
                · rcases h2bigk with h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c | h26280c
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26280_1]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h4, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h19744, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h22010, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h0, hlam, p26280_1]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h26245, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h26247, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h26249, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    rcases p26280_3 (m.d 0 2) (by simp) with h26291 | h26291
                    · linarith only [h26291, hlam, p26280_0]
                    · rcases p26280_3 (m.d 1 2) (by simp) with h26293 | h26293
                      · linarith only [h26245, h26293, hlam]
                      · rcases p26280_3 (m.d 2 3) (by simp) with h26295 | h26295
                        · rcases p26280_3 (m.d 2 4) (by simp) with h26296 | h26296
                          · linarith only [h26255, h26296, hlam]
                          · linarith only [h19744, h26296, hlam]
                        · linarith only [h26295, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    rcases p26280_3 (m.d 0 2) (by simp) with h26300 | h26300
                    · linarith only [h26300, h4, hlam]
                    · linarith only [h0, h26300, hlam]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h19744, h23339, h26257, hc02, hc23, hlam, hphi, p26280_1]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc23, hlam, hphi, p26280_1]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    rcases p26280_3 (m.d 0 2) (by simp) with h26306 | h26306
                    · linarith only [h26306, hlam, p26280_0]
                    · rcases p26280_3 (m.d 1 2) (by simp) with h26308 | h26308
                      · linarith only [h26247, h26308, hlam]
                      · rcases p26280_3 (m.d 2 3) (by simp) with h26310 | h26310
                        · rcases p26280_3 (m.d 2 4) (by simp) with h26311 | h26311
                          · rcases p26280_3 (m.d 2 5) (by simp) with h26312 | h26312
                            · linarith only [h26257, h26312, hlam]
                            · linarith only [h22010, h26312, hlam]
                          · linarith only [h26311, hlam, p26280_0]
                        · linarith only [h26310, h4, hlam]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    rcases p26280_3 (m.d 0 2) (by simp) with h26317 | h26317
                    · linarith only [h19744, h26317, hlam]
                    · linarith only [h0, h26317, hlam]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h26255, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26280_1]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    rcases p26280_3 (m.d 0 2) (by simp) with h26323 | h26323
                    · linarith only [h26323, hlam, p26280_0]
                    · rcases p26280_3 (m.d 1 2) (by simp) with h26325 | h26325
                      · linarith only [h26249, h26325, hlam]
                      · rcases p26280_3 (m.d 2 3) (by simp) with h26327 | h26327
                        · rcases p26280_3 (m.d 2 4) (by simp) with h26328 | h26328
                          · rcases p26280_3 (m.d 2 5) (by simp) with h26329 | h26329
                            · rcases h4bigk with h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c | h26330c
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h19744, hlam, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h23339, hc34, hc45, hlam, hphi, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h23339, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h2, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h26247, hlam, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h2, h23339, hc34, hc45, hlam, hphi, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h26253, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                rcases p26330_3 (m.d 0 4) (by simp) with h26341 | h26341
                                · linarith only [h19744, h26341, hlam]
                                · rcases p26330_3 (m.d 1 4) (by simp) with h26343 | h26343
                                  · linarith only [h26247, h26343, hlam]
                                  · rcases p26330_3 (m.d 2 4) (by simp) with h26345 | h26345
                                    · rcases p26330_3 (m.d 3 4) (by simp) with h26346 | h26346
                                      · linarith only [h26255, h26346, hlam]
                                      · rcases p26330_3 (m.d 4 5) (by simp) with h26348 | h26348
                                        · linarith only [h26257, h26348, hlam]
                                        · linarith only [h23339, h26348, hlam]
                                    · linarith only [h19744, h26345, hlam]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                rcases p26330_3 (m.d 0 4) (by simp) with h26352 | h26352
                                · linarith only [h19744, h26352, hlam]
                                · linarith only [h2, h26352, hlam]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                rcases p26330_3 (m.d 0 4) (by simp) with h26356 | h26356
                                · linarith only [h19744, h26356, hlam]
                                · linarith only [h23337, h26356, hlam]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h0, h19744, h23339, h26255, hc12, hc23, hlam, hphi, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h23337, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h26251, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h26255, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h26258, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h0, h19744, h26255, h26257, hc12, hc23, hlam, hphi, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h26247, h26255, h26257, hc12, hc23, hlam, hphi, p26330_1]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [h26257, hlam, p26330_0]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                rcases p26330_3 (m.d 0 4) (by simp) with h26368 | h26368
                                · linarith only [h23339, h26368, hlam]
                                · linarith only [h23337, h26368, hlam]
                              · have p26330_0 := h26330c.1
                                have p26330_1 := h26330c.2.1
                                have p26330_2 := h26330c.2.2.1
                                have p26330_3 := h26330c.2.2.2
                                linarith only [hlam, p26330_0]
                            · linarith only [h26329, hlam, p26280_0]
                          · linarith only [h19744, h26328, hlam]
                        · linarith only [h26327, h4, hlam]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    rcases p26280_3 (m.d 0 2) (by simp) with h26375 | h26375
                    · linarith only [h22010, h26375, hlam]
                    · linarith only [h0, h26375, hlam]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h26256, hlam, p26280_0]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [h26257, hlam, p26280_1]
                  · have p26280_0 := h26280c.1
                    have p26280_1 := h26280c.2.1
                    have p26280_2 := h26280c.2.2.1
                    have p26280_3 := h26280c.2.2.2
                    linarith only [hlam, p26280_0]
                · rcases h2bigk with h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c | h26381c
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p26381_1]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h4, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h19744, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h22010, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h0, hlam, p26381_1]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h26245, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h26247, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h26249, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    rcases p26381_3 (m.d 0 2) (by simp) with h26392 | h26392
                    · linarith only [h26392, hlam, p26381_0]
                    · rcases p26381_3 (m.d 1 2) (by simp) with h26394 | h26394
                      · linarith only [h26245, h26394, hlam]
                      · rcases p26381_3 (m.d 2 3) (by simp) with h26396 | h26396
                        · rcases p26381_3 (m.d 2 4) (by simp) with h26397 | h26397
                          · linarith only [h26255, h26397, hlam]
                          · linarith only [h19744, h26397, hlam]
                        · linarith only [h26396, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    rcases p26381_3 (m.d 0 2) (by simp) with h26401 | h26401
                    · linarith only [h26401, h4, hlam]
                    · linarith only [h0, h26401, hlam]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h19744, h23339, h26257, hc02, hc23, hlam, hphi, p26381_1]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p26381_1]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    rcases p26381_3 (m.d 0 2) (by simp) with h26407 | h26407
                    · linarith only [h26407, hlam, p26381_0]
                    · rcases p26381_3 (m.d 1 2) (by simp) with h26409 | h26409
                      · linarith only [h26247, h26409, hlam]
                      · rcases p26381_3 (m.d 2 3) (by simp) with h26411 | h26411
                        · rcases p26381_3 (m.d 2 4) (by simp) with h26412 | h26412
                          · rcases p26381_3 (m.d 2 5) (by simp) with h26413 | h26413
                            · linarith only [h26257, h26413, hlam]
                            · linarith only [h22010, h26413, hlam]
                          · linarith only [h26412, hlam, p26381_0]
                        · linarith only [h26411, h4, hlam]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    rcases p26381_3 (m.d 0 2) (by simp) with h26418 | h26418
                    · linarith only [h19744, h26418, hlam]
                    · linarith only [h0, h26418, hlam]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h26255, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26381_1]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    rcases p26381_3 (m.d 0 2) (by simp) with h26424 | h26424
                    · linarith only [h26424, hlam, p26381_0]
                    · rcases p26381_3 (m.d 1 2) (by simp) with h26426 | h26426
                      · linarith only [h26249, h26426, hlam]
                      · rcases p26381_3 (m.d 2 3) (by simp) with h26428 | h26428
                        · rcases p26381_3 (m.d 2 4) (by simp) with h26429 | h26429
                          · rcases p26381_3 (m.d 2 5) (by simp) with h26430 | h26430
                            · rcases h4bigk with h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c | h26431c
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h19744, hlam, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h23339, hc34, hc45, hlam, hphi, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h23339, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h2, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h26247, hlam, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h2, h23339, hc34, hc45, hlam, hphi, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h26253, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                rcases p26431_3 (m.d 0 4) (by simp) with h26442 | h26442
                                · linarith only [h19744, h26442, hlam]
                                · rcases p26431_3 (m.d 1 4) (by simp) with h26444 | h26444
                                  · linarith only [h26247, h26444, hlam]
                                  · rcases p26431_3 (m.d 2 4) (by simp) with h26446 | h26446
                                    · rcases p26431_3 (m.d 3 4) (by simp) with h26447 | h26447
                                      · linarith only [h26255, h26447, hlam]
                                      · rcases p26431_3 (m.d 4 5) (by simp) with h26449 | h26449
                                        · linarith only [h26257, h26449, hlam]
                                        · linarith only [h23339, h26449, hlam]
                                    · linarith only [h19744, h26446, hlam]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                rcases p26431_3 (m.d 0 4) (by simp) with h26453 | h26453
                                · linarith only [h19744, h26453, hlam]
                                · linarith only [h2, h26453, hlam]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                rcases p26431_3 (m.d 0 4) (by simp) with h26457 | h26457
                                · linarith only [h19744, h26457, hlam]
                                · linarith only [h23337, h26457, hlam]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h0, h19744, h23339, h26255, hc12, hc23, hlam, hphi, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h23337, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h26251, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h26255, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h26258, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h0, h19744, h26255, h26257, hc12, hc23, hlam, hphi, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h26247, h26255, h26257, hc12, hc23, hlam, hphi, p26431_1]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [h26257, hlam, p26431_0]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                rcases p26431_3 (m.d 0 4) (by simp) with h26469 | h26469
                                · linarith only [h23339, h26469, hlam]
                                · linarith only [h23337, h26469, hlam]
                              · have p26431_0 := h26431c.1
                                have p26431_1 := h26431c.2.1
                                have p26431_2 := h26431c.2.2.1
                                have p26431_3 := h26431c.2.2.2
                                linarith only [hlam, p26431_0]
                            · linarith only [h26430, hlam, p26381_0]
                          · linarith only [h19744, h26429, hlam]
                        · linarith only [h26428, h4, hlam]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    rcases p26381_3 (m.d 0 2) (by simp) with h26476 | h26476
                    · linarith only [h22010, h26476, hlam]
                    · linarith only [h0, h26476, hlam]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h26256, hlam, p26381_0]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [h26257, hlam, p26381_1]
                  · have p26381_0 := h26381c.1
                    have p26381_1 := h26381c.2.1
                    have p26381_2 := h26381c.2.2.1
                    have p26381_3 := h26381c.2.2.2
                    linarith only [hlam, p26381_0]
                · rcases h2bigk with h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c | h26482c
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p26482_1]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h4, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h19744, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h22010, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h0, hlam, p26482_1]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h26245, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h26247, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h26249, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    rcases p26482_3 (m.d 0 2) (by simp) with h26493 | h26493
                    · linarith only [h26493, hlam, p26482_0]
                    · rcases p26482_3 (m.d 1 2) (by simp) with h26495 | h26495
                      · linarith only [h26245, h26495, hlam]
                      · rcases p26482_3 (m.d 2 3) (by simp) with h26497 | h26497
                        · rcases p26482_3 (m.d 2 4) (by simp) with h26498 | h26498
                          · linarith only [h26255, h26498, hlam]
                          · linarith only [h19744, h26498, hlam]
                        · linarith only [h26497, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    rcases p26482_3 (m.d 0 2) (by simp) with h26502 | h26502
                    · linarith only [h26502, h4, hlam]
                    · linarith only [h0, h26502, hlam]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h19744, h23339, h26257, hc02, hc23, hlam, hphi, p26482_1]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p26482_1]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    rcases p26482_3 (m.d 0 2) (by simp) with h26508 | h26508
                    · linarith only [h26508, hlam, p26482_0]
                    · rcases p26482_3 (m.d 1 2) (by simp) with h26510 | h26510
                      · linarith only [h26247, h26510, hlam]
                      · rcases p26482_3 (m.d 2 3) (by simp) with h26512 | h26512
                        · rcases p26482_3 (m.d 2 4) (by simp) with h26513 | h26513
                          · rcases p26482_3 (m.d 2 5) (by simp) with h26514 | h26514
                            · linarith only [h26257, h26514, hlam]
                            · linarith only [h22010, h26514, hlam]
                          · linarith only [h26513, hlam, p26482_0]
                        · linarith only [h26512, h4, hlam]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    rcases p26482_3 (m.d 0 2) (by simp) with h26519 | h26519
                    · linarith only [h19744, h26519, hlam]
                    · linarith only [h0, h26519, hlam]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h26255, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26482_1]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    rcases p26482_3 (m.d 0 2) (by simp) with h26525 | h26525
                    · linarith only [h26525, hlam, p26482_0]
                    · rcases p26482_3 (m.d 1 2) (by simp) with h26527 | h26527
                      · linarith only [h26249, h26527, hlam]
                      · rcases p26482_3 (m.d 2 3) (by simp) with h26529 | h26529
                        · rcases p26482_3 (m.d 2 4) (by simp) with h26530 | h26530
                          · rcases p26482_3 (m.d 2 5) (by simp) with h26531 | h26531
                            · rcases h4bigk with h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c | h26532c
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h19744, hlam, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h23339, hc34, hc45, hlam, hphi, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h23339, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h2, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h26247, hlam, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h2, h23339, hc34, hc45, hlam, hphi, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h26253, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                rcases p26532_3 (m.d 0 4) (by simp) with h26543 | h26543
                                · linarith only [h19744, h26543, hlam]
                                · rcases p26532_3 (m.d 1 4) (by simp) with h26545 | h26545
                                  · linarith only [h26247, h26545, hlam]
                                  · rcases p26532_3 (m.d 2 4) (by simp) with h26547 | h26547
                                    · rcases p26532_3 (m.d 3 4) (by simp) with h26548 | h26548
                                      · linarith only [h26255, h26548, hlam]
                                      · rcases p26532_3 (m.d 4 5) (by simp) with h26550 | h26550
                                        · linarith only [h26257, h26550, hlam]
                                        · linarith only [h23339, h26550, hlam]
                                    · linarith only [h19744, h26547, hlam]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                rcases p26532_3 (m.d 0 4) (by simp) with h26554 | h26554
                                · linarith only [h19744, h26554, hlam]
                                · linarith only [h2, h26554, hlam]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                rcases p26532_3 (m.d 0 4) (by simp) with h26558 | h26558
                                · linarith only [h19744, h26558, hlam]
                                · linarith only [h23337, h26558, hlam]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h0, h19744, h23339, h26255, hc12, hc23, hlam, hphi, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h23337, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h26251, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h26255, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h26258, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h0, h19744, h26255, h26257, hc12, hc23, hlam, hphi, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h26247, h26255, h26257, hc12, hc23, hlam, hphi, p26532_1]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [h26257, hlam, p26532_0]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                rcases p26532_3 (m.d 0 4) (by simp) with h26570 | h26570
                                · linarith only [h23339, h26570, hlam]
                                · linarith only [h23337, h26570, hlam]
                              · have p26532_0 := h26532c.1
                                have p26532_1 := h26532c.2.1
                                have p26532_2 := h26532c.2.2.1
                                have p26532_3 := h26532c.2.2.2
                                linarith only [hlam, p26532_0]
                            · linarith only [h26531, hlam, p26482_0]
                          · linarith only [h19744, h26530, hlam]
                        · linarith only [h26529, h4, hlam]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    rcases p26482_3 (m.d 0 2) (by simp) with h26577 | h26577
                    · linarith only [h22010, h26577, hlam]
                    · linarith only [h0, h26577, hlam]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h26256, hlam, p26482_0]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [h26257, hlam, p26482_1]
                  · have p26482_0 := h26482c.1
                    have p26482_1 := h26482c.2.1
                    have p26482_2 := h26482c.2.2.1
                    have p26482_3 := h26482c.2.2.2
                    linarith only [hlam, p26482_0]
                · rcases h2bigk with h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c | h26583c
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p26583_1]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h4, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h19744, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h22010, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h0, hlam, p26583_1]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h26245, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h26247, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h26249, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    rcases p26583_3 (m.d 0 2) (by simp) with h26594 | h26594
                    · linarith only [h26594, hlam, p26583_0]
                    · rcases p26583_3 (m.d 1 2) (by simp) with h26596 | h26596
                      · linarith only [h26245, h26596, hlam]
                      · rcases p26583_3 (m.d 2 3) (by simp) with h26598 | h26598
                        · rcases p26583_3 (m.d 2 4) (by simp) with h26599 | h26599
                          · linarith only [h26255, h26599, hlam]
                          · linarith only [h19744, h26599, hlam]
                        · linarith only [h26598, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    rcases p26583_3 (m.d 0 2) (by simp) with h26603 | h26603
                    · linarith only [h26603, h4, hlam]
                    · linarith only [h0, h26603, hlam]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h19744, h23339, h26257, hc02, hc23, hlam, hphi, p26583_1]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p26583_1]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    rcases p26583_3 (m.d 0 2) (by simp) with h26609 | h26609
                    · linarith only [h26609, hlam, p26583_0]
                    · rcases p26583_3 (m.d 1 2) (by simp) with h26611 | h26611
                      · linarith only [h26247, h26611, hlam]
                      · rcases p26583_3 (m.d 2 3) (by simp) with h26613 | h26613
                        · rcases p26583_3 (m.d 2 4) (by simp) with h26614 | h26614
                          · rcases p26583_3 (m.d 2 5) (by simp) with h26615 | h26615
                            · linarith only [h26257, h26615, hlam]
                            · linarith only [h22010, h26615, hlam]
                          · linarith only [h26614, hlam, p26583_0]
                        · linarith only [h26613, h4, hlam]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    rcases p26583_3 (m.d 0 2) (by simp) with h26620 | h26620
                    · linarith only [h19744, h26620, hlam]
                    · linarith only [h0, h26620, hlam]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h26255, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26583_1]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    rcases p26583_3 (m.d 0 2) (by simp) with h26626 | h26626
                    · linarith only [h26626, hlam, p26583_0]
                    · rcases p26583_3 (m.d 1 2) (by simp) with h26628 | h26628
                      · linarith only [h26249, h26628, hlam]
                      · rcases p26583_3 (m.d 2 3) (by simp) with h26630 | h26630
                        · rcases p26583_3 (m.d 2 4) (by simp) with h26631 | h26631
                          · rcases p26583_3 (m.d 2 5) (by simp) with h26632 | h26632
                            · rcases h4bigk with h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c | h26633c
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h19744, hlam, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h23339, hc34, hc45, hlam, hphi, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h23339, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h2, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h26247, hlam, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h2, h23339, hc34, hc45, hlam, hphi, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h26253, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                rcases p26633_3 (m.d 0 4) (by simp) with h26644 | h26644
                                · linarith only [h19744, h26644, hlam]
                                · rcases p26633_3 (m.d 1 4) (by simp) with h26646 | h26646
                                  · linarith only [h26247, h26646, hlam]
                                  · rcases p26633_3 (m.d 2 4) (by simp) with h26648 | h26648
                                    · rcases p26633_3 (m.d 3 4) (by simp) with h26649 | h26649
                                      · linarith only [h26255, h26649, hlam]
                                      · rcases p26633_3 (m.d 4 5) (by simp) with h26651 | h26651
                                        · linarith only [h26257, h26651, hlam]
                                        · linarith only [h23339, h26651, hlam]
                                    · linarith only [h19744, h26648, hlam]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                rcases p26633_3 (m.d 0 4) (by simp) with h26655 | h26655
                                · linarith only [h19744, h26655, hlam]
                                · linarith only [h2, h26655, hlam]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                rcases p26633_3 (m.d 0 4) (by simp) with h26659 | h26659
                                · linarith only [h19744, h26659, hlam]
                                · linarith only [h23337, h26659, hlam]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h0, h19744, h23339, h26255, hc12, hc23, hlam, hphi, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h23337, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h26251, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h26255, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h26258, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h0, h19744, h26255, h26257, hc12, hc23, hlam, hphi, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h26247, h26255, h26257, hc12, hc23, hlam, hphi, p26633_1]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [h26257, hlam, p26633_0]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                rcases p26633_3 (m.d 0 4) (by simp) with h26671 | h26671
                                · linarith only [h23339, h26671, hlam]
                                · linarith only [h23337, h26671, hlam]
                              · have p26633_0 := h26633c.1
                                have p26633_1 := h26633c.2.1
                                have p26633_2 := h26633c.2.2.1
                                have p26633_3 := h26633c.2.2.2
                                linarith only [hlam, p26633_0]
                            · linarith only [h26632, hlam, p26583_0]
                          · linarith only [h19744, h26631, hlam]
                        · linarith only [h26630, h4, hlam]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    rcases p26583_3 (m.d 0 2) (by simp) with h26678 | h26678
                    · linarith only [h22010, h26678, hlam]
                    · linarith only [h0, h26678, hlam]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h26256, hlam, p26583_0]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [h26257, hlam, p26583_1]
                  · have p26583_0 := h26583c.1
                    have p26583_1 := h26583c.2.1
                    have p26583_2 := h26583c.2.2.1
                    have p26583_3 := h26583c.2.2.2
                    linarith only [hlam, p26583_0]
      · linarith only [h26269, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      rcases p26260_3 (m.d 0 1) (by simp) with h26685 | h26685
      · rcases p26260_3 (m.d 1 2) (by simp) with h26686 | h26686
        · linarith only [h0, h26686, hlam]
        · rcases p26260_3 (m.d 1 3) (by simp) with h26688 | h26688
          · linarith only [h1, h26688, hlam]
          · linarith only [h26251, h26688, hlam]
      · linarith only [h26685, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      rcases p26260_3 (m.d 0 1) (by simp) with h26692 | h26692
      · rcases p26260_3 (m.d 1 2) (by simp) with h26693 | h26693
        · linarith only [h0, h26693, hlam]
        · rcases p26260_3 (m.d 1 3) (by simp) with h26695 | h26695
          · linarith only [h1, h26695, hlam]
          · linarith only [h26252, h26695, hlam]
      · linarith only [h26692, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h0, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h26245, hlam, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h26247, hlam, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h26249, hlam, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h1, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      rcases p26260_3 (m.d 0 1) (by simp) with h26705 | h26705
      · rcases p26260_3 (m.d 1 2) (by simp) with h26706 | h26706
        · linarith only [h26245, h26706, hlam]
        · rcases p26260_3 (m.d 1 3) (by simp) with h26708 | h26708
          · rcases p26260_3 (m.d 1 4) (by simp) with h26709 | h26709
            · linarith only [h26251, h26709, hlam]
            · linarith only [h26247, h26709, hlam]
          · linarith only [h26245, h26708, hlam]
      · linarith only [h0, h26705, hlam]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      rcases p26260_3 (m.d 0 1) (by simp) with h26715 | h26715
      · rcases p26260_3 (m.d 1 2) (by simp) with h26716 | h26716
        · linarith only [h26245, h26716, hlam]
        · rcases p26260_3 (m.d 1 3) (by simp) with h26718 | h26718
          · rcases p26260_3 (m.d 1 4) (by simp) with h26719 | h26719
            · linarith only [h26251, h26719, hlam]
            · rcases p26260_3 (m.d 1 5) (by simp) with h26721 | h26721
              · linarith only [h26252, h26721, hlam]
              · linarith only [h26253, h26721, hlam]
          · linarith only [h26251, h26718, hlam]
      · linarith only [h2, h26715, hlam]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      rcases p26260_3 (m.d 0 1) (by simp) with h26726 | h26726
      · rcases p26260_3 (m.d 1 2) (by simp) with h26727 | h26727
        · linarith only [h26245, h26727, hlam]
        · rcases p26260_3 (m.d 1 3) (by simp) with h26729 | h26729
          · rcases p26260_3 (m.d 1 4) (by simp) with h26730 | h26730
            · linarith only [h26251, h26730, hlam]
            · rcases p26260_3 (m.d 1 5) (by simp) with h26732 | h26732
              · linarith only [h26252, h26732, hlam]
              · rcases h1emax with h26734 | h26734 | h26734 | h26734 | h26734
                · linarith only [h1, h26247, h26253, h26734, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p26260_1]
                · rcases h2bigk with h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c | h26736c
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p26736_1]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h4, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h19744, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h22010, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h0, hlam, p26736_1]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h26245, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h26247, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h26249, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    rcases p26736_3 (m.d 0 2) (by simp) with h26747 | h26747
                    · linarith only [h26747, hlam, p26736_0]
                    · rcases p26736_3 (m.d 1 2) (by simp) with h26749 | h26749
                      · linarith only [h26245, h26749, hlam]
                      · rcases p26736_3 (m.d 2 3) (by simp) with h26751 | h26751
                        · rcases p26736_3 (m.d 2 4) (by simp) with h26752 | h26752
                          · linarith only [h26255, h26752, hlam]
                          · linarith only [h19744, h26752, hlam]
                        · linarith only [h26751, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    rcases p26736_3 (m.d 0 2) (by simp) with h26756 | h26756
                    · linarith only [h26756, h4, hlam]
                    · linarith only [h0, h26756, hlam]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h19744, h23339, h26257, hc02, hc23, hlam, hphi, p26736_1]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p26736_1]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    rcases p26736_3 (m.d 0 2) (by simp) with h26762 | h26762
                    · linarith only [h26762, hlam, p26736_0]
                    · rcases p26736_3 (m.d 1 2) (by simp) with h26764 | h26764
                      · linarith only [h26247, h26764, hlam]
                      · rcases p26736_3 (m.d 2 3) (by simp) with h26766 | h26766
                        · rcases p26736_3 (m.d 2 4) (by simp) with h26767 | h26767
                          · rcases p26736_3 (m.d 2 5) (by simp) with h26768 | h26768
                            · linarith only [h26257, h26768, hlam]
                            · linarith only [h22010, h26768, hlam]
                          · linarith only [h26767, hlam, p26736_0]
                        · linarith only [h26766, h4, hlam]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    rcases p26736_3 (m.d 0 2) (by simp) with h26773 | h26773
                    · linarith only [h19744, h26773, hlam]
                    · linarith only [h0, h26773, hlam]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h26255, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26736_1]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    rcases p26736_3 (m.d 0 2) (by simp) with h26779 | h26779
                    · linarith only [h26779, hlam, p26736_0]
                    · rcases p26736_3 (m.d 1 2) (by simp) with h26781 | h26781
                      · linarith only [h26249, h26781, hlam]
                      · rcases p26736_3 (m.d 2 3) (by simp) with h26783 | h26783
                        · rcases p26736_3 (m.d 2 4) (by simp) with h26784 | h26784
                          · rcases p26736_3 (m.d 2 5) (by simp) with h26785 | h26785
                            · rcases h4bigk with h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c | h26786c
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h19744, hlam, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h23339, hc34, hc45, hlam, hphi, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h23339, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h2, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h26247, hlam, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h1, h26253, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p26260_1, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h26253, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                rcases p26786_3 (m.d 0 4) (by simp) with h26797 | h26797
                                · linarith only [h19744, h26797, hlam]
                                · rcases p26786_3 (m.d 1 4) (by simp) with h26799 | h26799
                                  · linarith only [h26247, h26799, hlam]
                                  · rcases p26786_3 (m.d 2 4) (by simp) with h26801 | h26801
                                    · rcases p26786_3 (m.d 3 4) (by simp) with h26802 | h26802
                                      · linarith only [h26255, h26802, hlam]
                                      · rcases p26786_3 (m.d 4 5) (by simp) with h26804 | h26804
                                        · linarith only [h26257, h26804, hlam]
                                        · linarith only [h23339, h26804, hlam]
                                    · linarith only [h19744, h26801, hlam]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                rcases p26786_3 (m.d 0 4) (by simp) with h26808 | h26808
                                · linarith only [h19744, h26808, hlam]
                                · linarith only [h2, h26808, hlam]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                rcases p26786_3 (m.d 0 4) (by simp) with h26812 | h26812
                                · linarith only [h19744, h26812, hlam]
                                · linarith only [h23337, h26812, hlam]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h0, h19744, h23339, h26255, hc12, hc23, hlam, hphi, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h23337, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h26251, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h26255, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h26258, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h0, h19744, h26255, h26257, hc12, hc23, hlam, hphi, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h26247, h26255, h26257, hc12, hc23, hlam, hphi, p26786_1]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [h26257, hlam, p26786_0]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                rcases p26786_3 (m.d 0 4) (by simp) with h26824 | h26824
                                · linarith only [h23339, h26824, hlam]
                                · linarith only [h23337, h26824, hlam]
                              · have p26786_0 := h26786c.1
                                have p26786_1 := h26786c.2.1
                                have p26786_2 := h26786c.2.2.1
                                have p26786_3 := h26786c.2.2.2
                                linarith only [hlam, p26786_0]
                            · linarith only [h26785, hlam, p26736_0]
                          · linarith only [h19744, h26784, hlam]
                        · linarith only [h26783, h4, hlam]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    rcases p26736_3 (m.d 0 2) (by simp) with h26831 | h26831
                    · linarith only [h22010, h26831, hlam]
                    · linarith only [h0, h26831, hlam]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h26256, hlam, p26736_0]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [h26257, hlam, p26736_1]
                  · have p26736_0 := h26736c.1
                    have p26736_1 := h26736c.2.1
                    have p26736_2 := h26736c.2.2.1
                    have p26736_3 := h26736c.2.2.2
                    linarith only [hlam, p26736_0]
                · linarith only [h26247, h26253, h26734, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p26260_1]
                · rcases h2bigk with h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c | h26838c
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p26838_1]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h4, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h19744, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h22010, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h0, hlam, p26838_1]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h26245, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h26247, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h26249, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    rcases p26838_3 (m.d 0 2) (by simp) with h26849 | h26849
                    · linarith only [h26849, hlam, p26838_0]
                    · rcases p26838_3 (m.d 1 2) (by simp) with h26851 | h26851
                      · linarith only [h26245, h26851, hlam]
                      · rcases p26838_3 (m.d 2 3) (by simp) with h26853 | h26853
                        · rcases p26838_3 (m.d 2 4) (by simp) with h26854 | h26854
                          · linarith only [h26255, h26854, hlam]
                          · linarith only [h19744, h26854, hlam]
                        · linarith only [h26853, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    rcases p26838_3 (m.d 0 2) (by simp) with h26858 | h26858
                    · linarith only [h26858, h4, hlam]
                    · linarith only [h0, h26858, hlam]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h19744, h23339, h26257, hc02, hc23, hlam, hphi, p26838_1]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p26838_1]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    rcases p26838_3 (m.d 0 2) (by simp) with h26864 | h26864
                    · linarith only [h26864, hlam, p26838_0]
                    · rcases p26838_3 (m.d 1 2) (by simp) with h26866 | h26866
                      · linarith only [h26247, h26866, hlam]
                      · rcases p26838_3 (m.d 2 3) (by simp) with h26868 | h26868
                        · rcases p26838_3 (m.d 2 4) (by simp) with h26869 | h26869
                          · rcases p26838_3 (m.d 2 5) (by simp) with h26870 | h26870
                            · linarith only [h26257, h26870, hlam]
                            · linarith only [h22010, h26870, hlam]
                          · linarith only [h26869, hlam, p26838_0]
                        · linarith only [h26868, h4, hlam]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    rcases p26838_3 (m.d 0 2) (by simp) with h26875 | h26875
                    · linarith only [h19744, h26875, hlam]
                    · linarith only [h0, h26875, hlam]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h26255, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26838_1]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    rcases p26838_3 (m.d 0 2) (by simp) with h26881 | h26881
                    · linarith only [h26881, hlam, p26838_0]
                    · rcases p26838_3 (m.d 1 2) (by simp) with h26883 | h26883
                      · linarith only [h26249, h26883, hlam]
                      · rcases p26838_3 (m.d 2 3) (by simp) with h26885 | h26885
                        · rcases p26838_3 (m.d 2 4) (by simp) with h26886 | h26886
                          · rcases p26838_3 (m.d 2 5) (by simp) with h26887 | h26887
                            · rcases h4bigk with h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c | h26888c
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h19744, hlam, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h23339, hc34, hc45, hlam, hphi, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h23339, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h2, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h26247, hlam, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h1, h26253, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p26260_1, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h26253, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                rcases p26888_3 (m.d 0 4) (by simp) with h26899 | h26899
                                · linarith only [h19744, h26899, hlam]
                                · rcases p26888_3 (m.d 1 4) (by simp) with h26901 | h26901
                                  · linarith only [h26247, h26901, hlam]
                                  · rcases p26888_3 (m.d 2 4) (by simp) with h26903 | h26903
                                    · rcases p26888_3 (m.d 3 4) (by simp) with h26904 | h26904
                                      · linarith only [h26255, h26904, hlam]
                                      · rcases p26888_3 (m.d 4 5) (by simp) with h26906 | h26906
                                        · linarith only [h26257, h26906, hlam]
                                        · linarith only [h23339, h26906, hlam]
                                    · linarith only [h19744, h26903, hlam]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                rcases p26888_3 (m.d 0 4) (by simp) with h26910 | h26910
                                · linarith only [h19744, h26910, hlam]
                                · linarith only [h2, h26910, hlam]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                rcases p26888_3 (m.d 0 4) (by simp) with h26914 | h26914
                                · linarith only [h19744, h26914, hlam]
                                · linarith only [h23337, h26914, hlam]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h0, h19744, h23339, h26255, hc12, hc23, hlam, hphi, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h23337, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h26251, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h26255, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h26258, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h0, h19744, h26255, h26257, hc12, hc23, hlam, hphi, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h26247, h26255, h26257, hc12, hc23, hlam, hphi, p26888_1]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [h26257, hlam, p26888_0]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                rcases p26888_3 (m.d 0 4) (by simp) with h26926 | h26926
                                · linarith only [h23339, h26926, hlam]
                                · linarith only [h23337, h26926, hlam]
                              · have p26888_0 := h26888c.1
                                have p26888_1 := h26888c.2.1
                                have p26888_2 := h26888c.2.2.1
                                have p26888_3 := h26888c.2.2.2
                                linarith only [hlam, p26888_0]
                            · linarith only [h26887, hlam, p26838_0]
                          · linarith only [h19744, h26886, hlam]
                        · linarith only [h26885, h4, hlam]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    rcases p26838_3 (m.d 0 2) (by simp) with h26933 | h26933
                    · linarith only [h22010, h26933, hlam]
                    · linarith only [h0, h26933, hlam]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h26256, hlam, p26838_0]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [h26257, hlam, p26838_1]
                  · have p26838_0 := h26838c.1
                    have p26838_1 := h26838c.2.1
                    have p26838_2 := h26838c.2.2.1
                    have p26838_3 := h26838c.2.2.2
                    linarith only [hlam, p26838_0]
                · rcases h2bigk with h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c | h26939c
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h4, hc12, hc23, hlam, hphi, p26939_1]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h4, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h19744, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h22010, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h0, hlam, p26939_1]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h26245, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h26247, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h26249, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    rcases p26939_3 (m.d 0 2) (by simp) with h26950 | h26950
                    · linarith only [h26950, hlam, p26939_0]
                    · rcases p26939_3 (m.d 1 2) (by simp) with h26952 | h26952
                      · linarith only [h26245, h26952, hlam]
                      · rcases p26939_3 (m.d 2 3) (by simp) with h26954 | h26954
                        · rcases p26939_3 (m.d 2 4) (by simp) with h26955 | h26955
                          · linarith only [h26255, h26955, hlam]
                          · linarith only [h19744, h26955, hlam]
                        · linarith only [h26954, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    rcases p26939_3 (m.d 0 2) (by simp) with h26959 | h26959
                    · linarith only [h26959, h4, hlam]
                    · linarith only [h0, h26959, hlam]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h19744, h23339, h26257, hc02, hc23, hlam, hphi, p26939_1]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h0, h22010, hc12, hc23, hlam, hphi, p26939_1]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    rcases p26939_3 (m.d 0 2) (by simp) with h26965 | h26965
                    · linarith only [h26965, hlam, p26939_0]
                    · rcases p26939_3 (m.d 1 2) (by simp) with h26967 | h26967
                      · linarith only [h26247, h26967, hlam]
                      · rcases p26939_3 (m.d 2 3) (by simp) with h26969 | h26969
                        · rcases p26939_3 (m.d 2 4) (by simp) with h26970 | h26970
                          · rcases p26939_3 (m.d 2 5) (by simp) with h26971 | h26971
                            · linarith only [h26257, h26971, hlam]
                            · linarith only [h22010, h26971, hlam]
                          · linarith only [h26970, hlam, p26939_0]
                        · linarith only [h26969, h4, hlam]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    rcases p26939_3 (m.d 0 2) (by simp) with h26976 | h26976
                    · linarith only [h19744, h26976, hlam]
                    · linarith only [h0, h26976, hlam]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h26255, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h0, h19744, h23339, h26257, hc12, hc24, hlam, hphi, p26939_1]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    rcases p26939_3 (m.d 0 2) (by simp) with h26982 | h26982
                    · linarith only [h26982, hlam, p26939_0]
                    · rcases p26939_3 (m.d 1 2) (by simp) with h26984 | h26984
                      · linarith only [h26249, h26984, hlam]
                      · rcases p26939_3 (m.d 2 3) (by simp) with h26986 | h26986
                        · rcases p26939_3 (m.d 2 4) (by simp) with h26987 | h26987
                          · rcases p26939_3 (m.d 2 5) (by simp) with h26988 | h26988
                            · rcases h4bigk with h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c | h26989c
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h23339, h26247, hc12, hc45, hlam, hphi, ht23, ht34, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h19744, hlam, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h23339, hc34, hc45, hlam, hphi, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h23339, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h2, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h26247, hlam, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h1, h26253, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p26260_1, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h26253, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                rcases p26989_3 (m.d 0 4) (by simp) with h27000 | h27000
                                · linarith only [h19744, h27000, hlam]
                                · rcases p26989_3 (m.d 1 4) (by simp) with h27002 | h27002
                                  · linarith only [h26247, h27002, hlam]
                                  · rcases p26989_3 (m.d 2 4) (by simp) with h27004 | h27004
                                    · rcases p26989_3 (m.d 3 4) (by simp) with h27005 | h27005
                                      · linarith only [h26255, h27005, hlam]
                                      · rcases p26989_3 (m.d 4 5) (by simp) with h27007 | h27007
                                        · linarith only [h26257, h27007, hlam]
                                        · linarith only [h23339, h27007, hlam]
                                    · linarith only [h19744, h27004, hlam]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                rcases p26989_3 (m.d 0 4) (by simp) with h27011 | h27011
                                · linarith only [h19744, h27011, hlam]
                                · linarith only [h2, h27011, hlam]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                rcases p26989_3 (m.d 0 4) (by simp) with h27015 | h27015
                                · linarith only [h19744, h27015, hlam]
                                · linarith only [h23337, h27015, hlam]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h0, h19744, h23339, h26255, hc12, hc23, hlam, hphi, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h23337, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h26251, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h26255, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h26258, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h0, h19744, h26255, h26257, hc12, hc23, hlam, hphi, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h26247, h26255, h26257, hc12, hc23, hlam, hphi, p26989_1]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [h26257, hlam, p26989_0]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                rcases p26989_3 (m.d 0 4) (by simp) with h27027 | h27027
                                · linarith only [h23339, h27027, hlam]
                                · linarith only [h23337, h27027, hlam]
                              · have p26989_0 := h26989c.1
                                have p26989_1 := h26989c.2.1
                                have p26989_2 := h26989c.2.2.1
                                have p26989_3 := h26989c.2.2.2
                                linarith only [hlam, p26989_0]
                            · linarith only [h26988, hlam, p26939_0]
                          · linarith only [h19744, h26987, hlam]
                        · linarith only [h26986, h4, hlam]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    rcases p26939_3 (m.d 0 2) (by simp) with h27034 | h27034
                    · linarith only [h22010, h27034, hlam]
                    · linarith only [h0, h27034, hlam]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h26256, hlam, p26939_0]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [h26257, hlam, p26939_1]
                  · have p26939_0 := h26939c.1
                    have p26939_1 := h26939c.2.1
                    have p26939_2 := h26939c.2.2.1
                    have p26939_3 := h26939c.2.2.2
                    linarith only [hlam, p26939_0]
          · linarith only [h26252, h26729, hlam]
      · linarith only [h26726, h3, hlam]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h2, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h2, h23339, h26255, h26257, hc12, hc23, hlam, hphi, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h26251, hlam, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h26253, hlam, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h3, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h23339, h26255, h26257, h3, hc12, hc23, hlam, hphi, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h26252, hlam, p26260_0]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [h23339, h26247, h26255, h26257, h3, hc12, hc23, hlam, hphi, p26260_1]
    · have p26260_0 := h26260c.1
      have p26260_1 := h26260c.2.1
      have p26260_2 := h26260c.2.2.1
      have p26260_3 := h26260c.2.2.2
      linarith only [hlam, p26260_0]

end R2N4
