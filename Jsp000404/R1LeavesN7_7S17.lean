import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h12243 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h12244 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h12245 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 2 3 5 (by decide) (by decide) with h12246 | h12246
  · rcases m.htr 2 4 5 (by decide) (by decide) with h12247 | h12247
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12248 | h12248
      · linarith only [h12233, h12245, h12248, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
      · rcases h1bigk with h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c | h12250c
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h0, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h10472, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h11379, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12013, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          rcases p12250_3 (m.d 0 1) (by simp) with h12256 | h12256
          · linarith only [h12256, hlam, p12250_0]
          · rcases p12250_3 (m.d 1 2) (by simp) with h12258 | h12258
            · rcases p12250_3 (m.d 1 3) (by simp) with h12259 | h12259
              · linarith only [h12239, h12259, hlam]
              · linarith only [h10472, h12259, hlam]
            · linarith only [h12258, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12013, h12242, h12244, hc01, hc12, hlam, hphi, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h11379, h12234, h12247, h12248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12013, hc01, hc12, hlam, hphi, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          rcases p12250_3 (m.d 0 1) (by simp) with h12267 | h12267
          · linarith only [h12267, hlam, p12250_0]
          · rcases p12250_3 (m.d 1 2) (by simp) with h12269 | h12269
            · rcases p12250_3 (m.d 1 3) (by simp) with h12270 | h12270
              · rcases p12250_3 (m.d 1 4) (by simp) with h12271 | h12271
                · linarith only [h12242, h12271, hlam]
                · linarith only [h11379, h12271, hlam]
              · linarith only [h12270, hlam, p12250_0]
            · linarith only [h0, h12269, hlam]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12239, hlam, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h11379, h12234, h12247, h12248, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12013, h12239, hc01, hc12, hlam, hphi, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          rcases p12250_3 (m.d 0 1) (by simp) with h12280 | h12280
          · linarith only [h12280, hlam, p12250_0]
          · rcases p12250_3 (m.d 1 2) (by simp) with h12282 | h12282
            · rcases p12250_3 (m.d 1 3) (by simp) with h12283 | h12283
              · rcases p12250_3 (m.d 1 4) (by simp) with h12284 | h12284
                · rcases p12250_3 (m.d 1 5) (by simp) with h12285 | h12285
                  · linarith only [h12244, h12285, hlam]
                  · linarith only [h12013, h12285, hlam]
                · linarith only [h12284, hlam, p12250_0]
              · linarith only [h10472, h12283, hlam]
            · linarith only [h0, h12282, hlam]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12240, hlam, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12242, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12013, hc01, hc14, hlam, hphi, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          rcases p12250_3 (m.d 0 1) (by simp) with h12295 | h12295
          · linarith only [h12295, hlam, p12250_0]
          · rcases p12250_3 (m.d 1 2) (by simp) with h12297 | h12297
            · rcases p12250_3 (m.d 1 3) (by simp) with h12298 | h12298
              · rcases p12250_3 (m.d 1 4) (by simp) with h12299 | h12299
                · rcases p12250_3 (m.d 1 5) (by simp) with h12300 | h12300
                  · rcases h1emax with h12301 | h12301 | h12301 | h12301 | h12301
                    · rcases h3bigk with h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c | h12302c
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h10472, hlam, p12302_1]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h10472, h12239, h12245, h12247, h12248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12302_1]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        rcases p12302_3 (m.d 0 3) (by simp) with h12306 | h12306
                        · rcases p12302_3 (m.d 1 3) (by simp) with h12307 | h12307
                          · rcases p12302_3 (m.d 2 3) (by simp) with h12308 | h12308
                            · linarith only [h12233, h12308, hlam]
                            · linarith only [h12245, h12308, hlam]
                          · linarith only [h12242, h12307, hlam]
                        · linarith only [h12306, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        rcases p12302_3 (m.d 0 3) (by simp) with h12313 | h12313
                        · rcases p12302_3 (m.d 1 3) (by simp) with h12314 | h12314
                          · rcases p12302_3 (m.d 2 3) (by simp) with h12315 | h12315
                            · linarith only [h12233, h12315, hlam]
                            · linarith only [h12246, h12315, hlam]
                          · linarith only [h12243, h12314, hlam]
                        · linarith only [h12313, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12233, h12239, h12245, h12247, h12248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12302_1]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12239, h12245, h12247, h12248, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12302_1]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        rcases p12302_3 (m.d 0 3) (by simp) with h12323 | h12323
                        · linarith only [h10472, h12323, hlam]
                        · linarith only [h12236, h12323, hlam]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        rcases p12302_3 (m.d 0 3) (by simp) with h12326 | h12326
                        · linarith only [h10472, h12326, hlam]
                        · linarith only [h12237, h12326, hlam]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12233, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12239, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        rcases p12302_3 (m.d 0 3) (by simp) with h12332 | h12332
                        · rcases p12302_3 (m.d 1 3) (by simp) with h12333 | h12333
                          · rcases p12302_3 (m.d 2 3) (by simp) with h12334 | h12334
                            · rcases p12302_3 (m.d 3 4) (by simp) with h12335 | h12335
                              · linarith only [h12335, hlam, p12302_0]
                              · rcases p12302_3 (m.d 3 5) (by simp) with h12337 | h12337
                                · linarith only [h12246, h12337, hlam]
                                · linarith only [h12248, h12337, hlam]
                            · linarith only [h12334, hlam, p12302_0]
                          · linarith only [h12242, h12333, hlam]
                        · linarith only [h12236, h12332, hlam]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h0, h12233, hc12, hlam, hphi, ht01, ht0b, ht5b, p12302_1, u5ehi3]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12236, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12242, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12245, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12248, hlam, p12302_1]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12237, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12243, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h12246, hlam, p12302_0]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [h0, h12233, h12246, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12302_1]
                      · have p12302_0 := h12302c.1
                        have p12302_1 := h12302c.2.1
                        have p12302_2 := h12302c.2.2.1
                        have p12302_3 := h12302c.2.2.2
                        linarith only [hlam, p12302_0]
                    · linarith only [h0, h12301, hc01, hlam]
                    · linarith only [h10472, h12301, hc01, hlam]
                    · linarith only [h12244, h12301, hc01, hlam, p12250_1]
                    · linarith only [h12301, hc01, hlam, p12250_1]
                  · linarith only [h12300, hlam, p12250_0]
                · linarith only [h11379, h12299, hlam]
              · linarith only [h10472, h12298, hlam]
            · linarith only [h0, h12297, hlam]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12241, hlam, p12250_1]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12243, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [h12244, hlam, p12250_0]
        · have p12250_0 := h12250c.1
          have p12250_1 := h12250c.2.1
          have p12250_2 := h12250c.2.2.1
          have p12250_3 := h12250c.2.2.2
          linarith only [hlam, p12250_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12366 | h12366
      · linarith only [h0, h12233, h12245, h12247, h12366, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c | h12368c
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h0, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h10472, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h11379, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12013, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          rcases p12368_3 (m.d 0 1) (by simp) with h12374 | h12374
          · linarith only [h12374, hlam, p12368_0]
          · rcases p12368_3 (m.d 1 2) (by simp) with h12376 | h12376
            · rcases p12368_3 (m.d 1 3) (by simp) with h12377 | h12377
              · linarith only [h12239, h12377, hlam]
              · linarith only [h10472, h12377, hlam]
            · linarith only [h12376, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h10472, hc01, hc12, hlam, hphi, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h11379, h12238, h12245, h12247, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12013, hc01, hc12, hlam, hphi, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          rcases p12368_3 (m.d 0 1) (by simp) with h12385 | h12385
          · linarith only [h12385, hlam, p12368_0]
          · rcases p12368_3 (m.d 1 2) (by simp) with h12387 | h12387
            · rcases p12368_3 (m.d 1 3) (by simp) with h12388 | h12388
              · rcases p12368_3 (m.d 1 4) (by simp) with h12389 | h12389
                · linarith only [h12242, h12389, hlam]
                · linarith only [h11379, h12389, hlam]
              · linarith only [h12388, hlam, p12368_0]
            · linarith only [h0, h12387, hlam]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12239, hlam, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h11379, h12238, h12245, h12247, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12013, h12239, hc01, hc12, hlam, hphi, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          rcases p12368_3 (m.d 0 1) (by simp) with h12398 | h12398
          · linarith only [h12398, hlam, p12368_0]
          · rcases p12368_3 (m.d 1 2) (by simp) with h12400 | h12400
            · rcases p12368_3 (m.d 1 3) (by simp) with h12401 | h12401
              · rcases p12368_3 (m.d 1 4) (by simp) with h12402 | h12402
                · rcases p12368_3 (m.d 1 5) (by simp) with h12403 | h12403
                  · linarith only [h12244, h12403, hlam]
                  · linarith only [h12013, h12403, hlam]
                · linarith only [h12402, hlam, p12368_0]
              · linarith only [h10472, h12401, hlam]
            · linarith only [h0, h12400, hlam]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12240, hlam, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12242, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12013, hc01, hc14, hlam, hphi, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          rcases p12368_3 (m.d 0 1) (by simp) with h12413 | h12413
          · linarith only [h12413, hlam, p12368_0]
          · rcases p12368_3 (m.d 1 2) (by simp) with h12415 | h12415
            · rcases p12368_3 (m.d 1 3) (by simp) with h12416 | h12416
              · rcases p12368_3 (m.d 1 4) (by simp) with h12417 | h12417
                · rcases p12368_3 (m.d 1 5) (by simp) with h12418 | h12418
                  · rcases h1emax with h12419 | h12419 | h12419 | h12419 | h12419
                    · rcases h3bigk with h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c | h12420c
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h10472, hlam, p12420_1]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12246, hc03, hlam, hphi, ht0b, ht5b, p12420_1, u5ehi3]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        rcases p12420_3 (m.d 0 3) (by simp) with h12424 | h12424
                        · rcases p12420_3 (m.d 1 3) (by simp) with h12425 | h12425
                          · rcases p12420_3 (m.d 2 3) (by simp) with h12426 | h12426
                            · linarith only [h12233, h12426, hlam]
                            · linarith only [h12245, h12426, hlam]
                          · linarith only [h12242, h12425, hlam]
                        · linarith only [h12424, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        rcases p12420_3 (m.d 0 3) (by simp) with h12431 | h12431
                        · rcases p12420_3 (m.d 1 3) (by simp) with h12432 | h12432
                          · rcases p12420_3 (m.d 2 3) (by simp) with h12433 | h12433
                            · linarith only [h12233, h12433, hlam]
                            · linarith only [h12246, h12433, hlam]
                          · linarith only [h12243, h12432, hlam]
                        · linarith only [h12431, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12233, h12239, h12246, hc12, hlam, hphi, ht01, ht0b, ht5b, p12420_1, u5ehi3]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12239, h12246, hc12, hlam, hphi, ht01, ht0b, ht5b, p12420_1, u5ehi3]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        rcases p12420_3 (m.d 0 3) (by simp) with h12441 | h12441
                        · linarith only [h10472, h12441, hlam]
                        · linarith only [h12236, h12441, hlam]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        rcases p12420_3 (m.d 0 3) (by simp) with h12444 | h12444
                        · linarith only [h10472, h12444, hlam]
                        · linarith only [h12237, h12444, hlam]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12233, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12239, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        rcases p12420_3 (m.d 0 3) (by simp) with h12450 | h12450
                        · rcases p12420_3 (m.d 1 3) (by simp) with h12451 | h12451
                          · rcases p12420_3 (m.d 2 3) (by simp) with h12452 | h12452
                            · rcases p12420_3 (m.d 3 4) (by simp) with h12453 | h12453
                              · linarith only [h12453, hlam, p12420_0]
                              · rcases p12420_3 (m.d 3 5) (by simp) with h12455 | h12455
                                · linarith only [h12246, h12455, hlam]
                                · linarith only [h12366, h12455, hlam]
                            · linarith only [h12452, hlam, p12420_0]
                          · linarith only [h12242, h12451, hlam]
                        · linarith only [h12236, h12450, hlam]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h0, h12233, hc12, hlam, hphi, ht01, ht0b, ht5b, p12420_1, u5ehi3]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12236, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12242, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12245, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12366, hlam, p12420_1]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12237, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12243, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h12246, hlam, p12420_0]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [h0, h12233, h12246, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12420_1]
                      · have p12420_0 := h12420c.1
                        have p12420_1 := h12420c.2.1
                        have p12420_2 := h12420c.2.2.1
                        have p12420_3 := h12420c.2.2.2
                        linarith only [hlam, p12420_0]
                    · linarith only [h0, h12419, hc01, hlam]
                    · linarith only [h12242, h12244, h12419, hc01, hlam, p12368_1]
                    · linarith only [h12244, h12419, hc01, hlam, p12368_1]
                    · linarith only [h12419, hc01, hlam, p12368_1]
                  · linarith only [h12418, hlam, p12368_0]
                · linarith only [h11379, h12417, hlam]
              · linarith only [h10472, h12416, hlam]
            · linarith only [h0, h12415, hlam]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12241, hlam, p12368_1]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12243, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [h12244, hlam, p12368_0]
        · have p12368_0 := h12368c.1
          have p12368_1 := h12368c.2.1
          have p12368_2 := h12368c.2.2.1
          have p12368_3 := h12368c.2.2.2
          linarith only [hlam, p12368_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h12484 | h12484
    · linarith only [h12233, h12237, h12245, h12246, h12484, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12486 | h12486
      · linarith only [h10472, h12237, h12239, h12245, h12246, h12484, h12486, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c | h12488c
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h0, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h10472, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h11379, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12013, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          rcases p12488_3 (m.d 0 1) (by simp) with h12494 | h12494
          · linarith only [h12494, hlam, p12488_0]
          · rcases p12488_3 (m.d 1 2) (by simp) with h12496 | h12496
            · rcases p12488_3 (m.d 1 3) (by simp) with h12497 | h12497
              · linarith only [h12239, h12497, hlam]
              · linarith only [h10472, h12497, hlam]
            · linarith only [h12496, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h10472, h12236, h12238, h12246, h12486, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h11379, h12238, h12246, h12486, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12013, hc01, hc12, hlam, hphi, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          rcases p12488_3 (m.d 0 1) (by simp) with h12505 | h12505
          · linarith only [h12505, hlam, p12488_0]
          · rcases p12488_3 (m.d 1 2) (by simp) with h12507 | h12507
            · rcases p12488_3 (m.d 1 3) (by simp) with h12508 | h12508
              · rcases p12488_3 (m.d 1 4) (by simp) with h12509 | h12509
                · linarith only [h12242, h12509, hlam]
                · linarith only [h11379, h12509, hlam]
              · linarith only [h12508, hlam, p12488_0]
            · linarith only [h0, h12507, hlam]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12239, hlam, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h11379, h12238, h12245, h12246, h12486, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12013, h12238, h12239, h12245, h12246, h12486, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          rcases p12488_3 (m.d 0 1) (by simp) with h12518 | h12518
          · linarith only [h12518, hlam, p12488_0]
          · rcases p12488_3 (m.d 1 2) (by simp) with h12520 | h12520
            · rcases p12488_3 (m.d 1 3) (by simp) with h12521 | h12521
              · rcases p12488_3 (m.d 1 4) (by simp) with h12522 | h12522
                · rcases p12488_3 (m.d 1 5) (by simp) with h12523 | h12523
                  · linarith only [h12244, h12523, hlam]
                  · linarith only [h12013, h12523, hlam]
                · linarith only [h12522, hlam, p12488_0]
              · linarith only [h10472, h12521, hlam]
            · linarith only [h0, h12520, hlam]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12240, hlam, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12242, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12013, h12238, h12245, h12246, h12486, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          rcases p12488_3 (m.d 0 1) (by simp) with h12533 | h12533
          · linarith only [h12533, hlam, p12488_0]
          · rcases p12488_3 (m.d 1 2) (by simp) with h12535 | h12535
            · rcases p12488_3 (m.d 1 3) (by simp) with h12536 | h12536
              · rcases p12488_3 (m.d 1 4) (by simp) with h12537 | h12537
                · rcases p12488_3 (m.d 1 5) (by simp) with h12538 | h12538
                  · rcases h1emax with h12539 | h12539 | h12539 | h12539 | h12539
                    · rcases h3bigk with h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c | h12540c
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h10472, hlam, p12540_1]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        rcases p12540_3 (m.d 0 3) (by simp) with h12543 | h12543
                        · rcases p12540_3 (m.d 1 3) (by simp) with h12544 | h12544
                          · rcases p12540_3 (m.d 2 3) (by simp) with h12545 | h12545
                            · linarith only [h12233, h12545, hlam]
                            · rcases p12540_3 (m.d 3 4) (by simp) with h12547 | h12547
                              · linarith only [h12236, h12547, hlam]
                              · rcases p12540_3 (m.d 3 5) (by simp) with h12549 | h12549
                                · linarith only [h12237, h12549, hlam]
                                · linarith only [h12246, h12549, hlam]
                          · linarith only [h12239, h12544, hlam]
                        · linarith only [h12233, h12543, hlam]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12236, h12238, h12245, h12246, h12486, hlam, p12540_2]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12233, h12245, h12246, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p12540_1]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12236, h12238, h12239, h12245, h12246, h12486, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12540_1]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        rcases p12540_3 (m.d 0 3) (by simp) with h12558 | h12558
                        · linarith only [h10472, h12558, hlam]
                        · linarith only [h12233, h12558, hlam]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h10472, h12236, h12238, h12245, h12246, h12486, hlam, p12540_2]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12245, h12246, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12540_1]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12233, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12239, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12236, h12238, h12246, h12486, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12540_1]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12246, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12236, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12242, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12245, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12486, hlam, p12540_1]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12237, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h12243, hlam, p12540_0]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [h0, h12233, h12236, h12238, h12245, h12486, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12540_1]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        rcases p12540_3 (m.d 0 3) (by simp) with h12576 | h12576
                        · rcases p12540_3 (m.d 1 3) (by simp) with h12577 | h12577
                          · rcases p12540_3 (m.d 2 3) (by simp) with h12578 | h12578
                            · linarith only [h12246, h12578, hlam]
                            · linarith only [h12245, h12578, hlam]
                          · linarith only [h12242, h12577, hlam]
                        · linarith only [h12236, h12576, hlam]
                      · have p12540_0 := h12540c.1
                        have p12540_1 := h12540c.2.1
                        have p12540_2 := h12540c.2.2.1
                        have p12540_3 := h12540c.2.2.2
                        linarith only [hlam, p12540_0]
                    · linarith only [h0, h12233, h12236, h12238, h12486, h12539, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h10472, h12236, h12238, h12245, h12246, h12486, h12539, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11379, h12238, h12245, h12246, h12486, h12539, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h12539, hc01, hlam, p12488_1]
                  · linarith only [h12538, hlam, p12488_0]
                · linarith only [h11379, h12537, hlam]
              · linarith only [h10472, h12536, hlam]
            · linarith only [h0, h12535, hlam]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12241, hlam, p12488_1]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12243, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [h12244, hlam, p12488_0]
        · have p12488_0 := h12488c.1
          have p12488_1 := h12488c.2.1
          have p12488_2 := h12488c.2.2.1
          have p12488_3 := h12488c.2.2.2
          linarith only [hlam, p12488_0]

end R2N4
