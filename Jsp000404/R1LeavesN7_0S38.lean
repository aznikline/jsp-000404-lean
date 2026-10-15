import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x0 (m : N7Model)
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
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 2 3 4 (by decide) (by decide) with h23349 | h23349
  · rcases m.htr 2 3 5 (by decide) (by decide) with h23350 | h23350
    · rcases m.htr 2 4 5 (by decide) (by decide) with h23351 | h23351
      · rcases m.htr 3 4 5 (by decide) (by decide) with h23352 | h23352
        · rcases h1bigk with h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c | h23353c
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23355 | h23355
            · rcases p23353_3 (m.d 1 2) (by simp) with h23356 | h23356
              · linarith only [h23356, hlam, p23353_0]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23358 | h23358
                · linarith only [h1, h23358, hlam]
                · linarith only [h23340, h23358, hlam]
            · linarith only [h23355, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h23346, h23352, hc01, hc45, hlam, hphi, ht0b, ht5b, p23353_1]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23363 | h23363
            · rcases p23353_3 (m.d 1 2) (by simp) with h23364 | h23364
              · linarith only [h0, h23364, hlam]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23366 | h23366
                · linarith only [h1, h23366, hlam]
                · linarith only [h23346, h23366, hlam]
            · linarith only [h23363, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23370 | h23370
            · rcases p23353_3 (m.d 1 2) (by simp) with h23371 | h23371
              · linarith only [h0, h23371, hlam]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23373 | h23373
                · linarith only [h1, h23373, hlam]
                · linarith only [h23347, h23373, hlam]
            · linarith only [h23370, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h0, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h23340, hlam, p23353_1]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h23342, hlam, p23353_1]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h23344, hlam, p23353_1]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h1, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23383 | h23383
            · rcases p23353_3 (m.d 1 2) (by simp) with h23384 | h23384
              · linarith only [h23340, h23384, hlam]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23386 | h23386
                · rcases p23353_3 (m.d 1 4) (by simp) with h23387 | h23387
                  · linarith only [h23346, h23387, hlam]
                  · linarith only [h23342, h23387, hlam]
                · linarith only [h23340, h23386, hlam]
            · linarith only [h0, h23383, hlam]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h1, h23346, h23352, hc01, hc45, hlam, hphi, ht0b, ht5b, p23353_1]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23394 | h23394
            · rcases p23353_3 (m.d 1 2) (by simp) with h23395 | h23395
              · linarith only [h23340, h23395, hlam]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23397 | h23397
                · rcases p23353_3 (m.d 1 4) (by simp) with h23398 | h23398
                  · linarith only [h23346, h23398, hlam]
                  · linarith only [h23348, h23398, hlam]
                · linarith only [h23347, h23397, hlam]
            · linarith only [h23394, h3, hlam]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h2, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23404 | h23404
            · rcases p23353_3 (m.d 1 2) (by simp) with h23405 | h23405
              · linarith only [h23342, h23405, hlam]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23407 | h23407
                · rcases p23353_3 (m.d 1 4) (by simp) with h23408 | h23408
                  · rcases p23353_3 (m.d 1 5) (by simp) with h23409 | h23409
                    · linarith only [h23348, h23409, hlam]
                    · linarith only [h23344, h23409, hlam]
                  · linarith only [h23342, h23408, hlam]
                · linarith only [h23340, h23407, hlam]
            · linarith only [h0, h23404, hlam]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h23346, hlam, p23353_1]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23417 | h23417
            · rcases p23353_3 (m.d 1 2) (by simp) with h23418 | h23418
              · linarith only [h23342, h23418, hlam]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23420 | h23420
                · rcases p23353_3 (m.d 1 4) (by simp) with h23421 | h23421
                  · rcases p23353_3 (m.d 1 5) (by simp) with h23422 | h23422
                    · linarith only [h23348, h23422, hlam]
                    · rcases h1emax with h23424 | h23424 | h23424 | h23424 | h23424
                      · linarith only [h2, h23344, h23424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23353_1]
                      · rcases h2bigk with h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c | h23426c
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h22010, hc12, hc25, hlam, hphi, p23426_1]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h4, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h19744, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h22010, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h0, hlam, p23426_1]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h23340, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h23342, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h23344, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          rcases p23426_3 (m.d 0 2) (by simp) with h23437 | h23437
                          · linarith only [h23437, hlam, p23426_0]
                          · rcases p23426_3 (m.d 1 2) (by simp) with h23439 | h23439
                            · linarith only [h23340, h23439, hlam]
                            · rcases p23426_3 (m.d 2 3) (by simp) with h23441 | h23441
                              · rcases p23426_3 (m.d 2 4) (by simp) with h23442 | h23442
                                · linarith only [h23349, h23442, hlam]
                                · linarith only [h19744, h23442, hlam]
                              · linarith only [h23441, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          rcases p23426_3 (m.d 0 2) (by simp) with h23446 | h23446
                          · linarith only [h23446, h4, hlam]
                          · linarith only [h0, h23446, hlam]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h19744, h2, h23344, hc12, hc23, hlam, hphi, p23353_1, p23426_1]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h22010, hc02, hc23, hlam, hphi, p23426_1]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          rcases p23426_3 (m.d 0 2) (by simp) with h23452 | h23452
                          · linarith only [h23452, hlam, p23426_0]
                          · rcases p23426_3 (m.d 1 2) (by simp) with h23454 | h23454
                            · linarith only [h23342, h23454, hlam]
                            · rcases p23426_3 (m.d 2 3) (by simp) with h23456 | h23456
                              · rcases p23426_3 (m.d 2 4) (by simp) with h23457 | h23457
                                · rcases p23426_3 (m.d 2 5) (by simp) with h23458 | h23458
                                  · linarith only [h23351, h23458, hlam]
                                  · linarith only [h22010, h23458, hlam]
                                · linarith only [h23457, hlam, p23426_0]
                              · linarith only [h23456, h4, hlam]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          rcases p23426_3 (m.d 0 2) (by simp) with h23463 | h23463
                          · linarith only [h19744, h23463, hlam]
                          · linarith only [h0, h23463, hlam]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h23349, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h0, h22010, hc12, hc24, hlam, hphi, p23426_1]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          rcases p23426_3 (m.d 0 2) (by simp) with h23469 | h23469
                          · linarith only [h23469, hlam, p23426_0]
                          · rcases p23426_3 (m.d 1 2) (by simp) with h23471 | h23471
                            · linarith only [h23344, h23471, hlam]
                            · rcases p23426_3 (m.d 2 3) (by simp) with h23473 | h23473
                              · rcases p23426_3 (m.d 2 4) (by simp) with h23474 | h23474
                                · rcases p23426_3 (m.d 2 5) (by simp) with h23475 | h23475
                                  · rcases h4bigk with h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c | h23476c
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23337, h23344, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23353_1, p23476_1]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h19744, hlam, p23476_1]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      rcases p23476_3 (m.d 0 4) (by simp) with h23480 | h23480
                                      · rcases p23476_3 (m.d 1 4) (by simp) with h23481 | h23481
                                        · linarith only [h2, h23481, hlam]
                                        · linarith only [h23346, h23481, hlam]
                                      · linarith only [h23337, h23480, hlam]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      rcases p23476_3 (m.d 0 4) (by simp) with h23485 | h23485
                                      · rcases p23476_3 (m.d 1 4) (by simp) with h23486 | h23486
                                        · linarith only [h2, h23486, hlam]
                                        · linarith only [h23348, h23486, hlam]
                                      · linarith only [h23485, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h2, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23342, hlam, p23476_1]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h1, h23346, h23352, hc01, hc45, hlam, hphi, ht0b, ht5b, p23476_1]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      rcases p23476_3 (m.d 0 4) (by simp) with h23494 | h23494
                                      · rcases p23476_3 (m.d 1 4) (by simp) with h23495 | h23495
                                        · rcases p23476_3 (m.d 2 4) (by simp) with h23496 | h23496
                                          · rcases p23476_3 (m.d 3 4) (by simp) with h23497 | h23497
                                            · linarith only [h23346, h23497, hlam]
                                            · linarith only [h23352, h23497, hlam]
                                          · linarith only [h23351, h23496, hlam]
                                        · linarith only [h23495, hlam, p23476_0]
                                      · linarith only [h23339, h23494, hlam]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h2, h23344, h23349, hc12, hc23, hlam, hphi, p23353_1, p23476_1]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23344, h23349, hc12, hc23, hlam, hphi, p23353_1, p23476_1]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      rcases p23476_3 (m.d 0 4) (by simp) with h23506 | h23506
                                      · linarith only [h19744, h23506, hlam]
                                      · linarith only [h23337, h23506, hlam]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      rcases p23476_3 (m.d 0 4) (by simp) with h23509 | h23509
                                      · linarith only [h19744, h23509, hlam]
                                      · linarith only [h23339, h23509, hlam]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23337, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23346, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23349, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h1, h23346, hc01, hc45, hlam, hphi, ht0b, ht5b, p23476_1]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23339, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23348, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23351, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [h23352, hlam, p23476_0]
                                    · have p23476_0 := h23476c.1
                                      have p23476_1 := h23476c.2.1
                                      have p23476_2 := h23476c.2.2.1
                                      have p23476_3 := h23476c.2.2.2
                                      linarith only [hlam, p23476_0]
                                  · linarith only [h23475, hlam, p23426_0]
                                · linarith only [h19744, h23474, hlam]
                              · linarith only [h23473, h4, hlam]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          rcases p23426_3 (m.d 0 2) (by simp) with h23525 | h23525
                          · linarith only [h22010, h23525, hlam]
                          · linarith only [h0, h23525, hlam]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h23350, hlam, p23426_0]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [h23351, hlam, p23426_1]
                        · have p23426_0 := h23426c.1
                          have p23426_1 := h23426c.2.1
                          have p23426_2 := h23426c.2.2.1
                          have p23426_3 := h23426c.2.2.2
                          linarith only [hlam, p23426_0]
                      · linarith only [h23344, h23346, h23424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23353_1]
                      · linarith only [h23344, h23424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23353_1]
                      · rcases h2bigk with h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c | h23533c
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p23533_1]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h4, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h19744, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h22010, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h0, hlam, p23533_1]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h23340, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h23342, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h23344, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          rcases p23533_3 (m.d 0 2) (by simp) with h23544 | h23544
                          · linarith only [h23544, hlam, p23533_0]
                          · rcases p23533_3 (m.d 1 2) (by simp) with h23546 | h23546
                            · linarith only [h23340, h23546, hlam]
                            · rcases p23533_3 (m.d 2 3) (by simp) with h23548 | h23548
                              · rcases p23533_3 (m.d 2 4) (by simp) with h23549 | h23549
                                · linarith only [h23349, h23549, hlam]
                                · linarith only [h19744, h23549, hlam]
                              · linarith only [h23548, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          rcases p23533_3 (m.d 0 2) (by simp) with h23553 | h23553
                          · linarith only [h23553, h4, hlam]
                          · linarith only [h0, h23553, hlam]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h19744, hc02, hc23, hlam, hphi, p23533_1]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h0, h22010, hc12, hc23, hlam, hphi, p23533_1]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          rcases p23533_3 (m.d 0 2) (by simp) with h23559 | h23559
                          · linarith only [h23559, hlam, p23533_0]
                          · rcases p23533_3 (m.d 1 2) (by simp) with h23561 | h23561
                            · linarith only [h23342, h23561, hlam]
                            · rcases p23533_3 (m.d 2 3) (by simp) with h23563 | h23563
                              · rcases p23533_3 (m.d 2 4) (by simp) with h23564 | h23564
                                · rcases p23533_3 (m.d 2 5) (by simp) with h23565 | h23565
                                  · linarith only [h23351, h23565, hlam]
                                  · linarith only [h22010, h23565, hlam]
                                · linarith only [h23564, hlam, p23533_0]
                              · linarith only [h23563, h4, hlam]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          rcases p23533_3 (m.d 0 2) (by simp) with h23570 | h23570
                          · linarith only [h19744, h23570, hlam]
                          · linarith only [h0, h23570, hlam]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h23349, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h0, h22010, hc12, hc24, hlam, hphi, p23533_1]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          rcases p23533_3 (m.d 0 2) (by simp) with h23576 | h23576
                          · linarith only [h23576, hlam, p23533_0]
                          · rcases p23533_3 (m.d 1 2) (by simp) with h23578 | h23578
                            · linarith only [h23344, h23578, hlam]
                            · rcases p23533_3 (m.d 2 3) (by simp) with h23580 | h23580
                              · rcases p23533_3 (m.d 2 4) (by simp) with h23581 | h23581
                                · rcases p23533_3 (m.d 2 5) (by simp) with h23582 | h23582
                                  · rcases h4bigk with h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c | h23583c
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23344, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23353_1, p23583_1]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h19744, hlam, p23583_1]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      rcases p23583_3 (m.d 0 4) (by simp) with h23587 | h23587
                                      · rcases p23583_3 (m.d 1 4) (by simp) with h23588 | h23588
                                        · linarith only [h2, h23588, hlam]
                                        · linarith only [h23346, h23588, hlam]
                                      · linarith only [h23337, h23587, hlam]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      rcases p23583_3 (m.d 0 4) (by simp) with h23592 | h23592
                                      · rcases p23583_3 (m.d 1 4) (by simp) with h23593 | h23593
                                        · linarith only [h2, h23593, hlam]
                                        · linarith only [h23348, h23593, hlam]
                                      · linarith only [h23592, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h2, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23342, hlam, p23583_1]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h1, h23346, h23352, hc01, hc45, hlam, hphi, ht0b, ht5b, p23583_1]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      rcases p23583_3 (m.d 0 4) (by simp) with h23601 | h23601
                                      · rcases p23583_3 (m.d 1 4) (by simp) with h23602 | h23602
                                        · rcases p23583_3 (m.d 2 4) (by simp) with h23603 | h23603
                                          · rcases p23583_3 (m.d 3 4) (by simp) with h23604 | h23604
                                            · linarith only [h23346, h23604, hlam]
                                            · linarith only [h23352, h23604, hlam]
                                          · linarith only [h23351, h23603, hlam]
                                        · linarith only [h23602, hlam, p23583_0]
                                      · linarith only [h23339, h23601, hlam]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h2, h23344, h23349, hc12, hc23, hlam, hphi, p23353_1, p23583_1]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23344, h23349, hc12, hc23, hlam, hphi, p23353_1, p23583_1]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      rcases p23583_3 (m.d 0 4) (by simp) with h23613 | h23613
                                      · linarith only [h19744, h23613, hlam]
                                      · linarith only [h23337, h23613, hlam]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      rcases p23583_3 (m.d 0 4) (by simp) with h23616 | h23616
                                      · linarith only [h19744, h23616, hlam]
                                      · linarith only [h23339, h23616, hlam]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23337, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23346, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23349, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h1, h23346, hc01, hc45, hlam, hphi, ht0b, ht5b, p23583_1]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23339, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23348, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23351, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [h23352, hlam, p23583_0]
                                    · have p23583_0 := h23583c.1
                                      have p23583_1 := h23583c.2.1
                                      have p23583_2 := h23583c.2.2.1
                                      have p23583_3 := h23583c.2.2.2
                                      linarith only [hlam, p23583_0]
                                  · linarith only [h23582, hlam, p23533_0]
                                · linarith only [h19744, h23581, hlam]
                              · linarith only [h23580, h4, hlam]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          rcases p23533_3 (m.d 0 2) (by simp) with h23632 | h23632
                          · linarith only [h22010, h23632, hlam]
                          · linarith only [h0, h23632, hlam]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h23350, hlam, p23533_0]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [h23351, hlam, p23533_1]
                        · have p23533_0 := h23533c.1
                          have p23533_1 := h23533c.2.1
                          have p23533_2 := h23533c.2.2.1
                          have p23533_3 := h23533c.2.2.2
                          linarith only [hlam, p23533_0]
                  · linarith only [h23348, h23421, hlam]
                · linarith only [h23347, h23420, hlam]
            · linarith only [h23417, h3, hlam]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h3, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            rcases p23353_3 (m.d 0 1) (by simp) with h23642 | h23642
            · rcases p23353_3 (m.d 1 2) (by simp) with h23643 | h23643
              · linarith only [h23344, h23643, hlam]
              · rcases p23353_3 (m.d 1 3) (by simp) with h23645 | h23645
                · rcases p23353_3 (m.d 1 4) (by simp) with h23646 | h23646
                  · rcases p23353_3 (m.d 1 5) (by simp) with h23647 | h23647
                    · rcases h1emax with h23648 | h23648 | h23648 | h23648 | h23648
                      · linarith only [h1, h23346, h23648, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c | h23650c
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p23650_1]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h4, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h19744, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h22010, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h0, hlam, p23650_1]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h23340, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h23342, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h23344, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          rcases p23650_3 (m.d 0 2) (by simp) with h23661 | h23661
                          · linarith only [h23661, hlam, p23650_0]
                          · rcases p23650_3 (m.d 1 2) (by simp) with h23663 | h23663
                            · linarith only [h23340, h23663, hlam]
                            · rcases p23650_3 (m.d 2 3) (by simp) with h23665 | h23665
                              · rcases p23650_3 (m.d 2 4) (by simp) with h23666 | h23666
                                · linarith only [h23349, h23666, hlam]
                                · linarith only [h19744, h23666, hlam]
                              · linarith only [h23665, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          rcases p23650_3 (m.d 0 2) (by simp) with h23670 | h23670
                          · linarith only [h23670, h4, hlam]
                          · linarith only [h0, h23670, hlam]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h19744, hc02, hc23, hlam, hphi, p23650_1]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h22010, h3, hc12, hc23, hlam, hphi, p23353_1, p23650_1]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          rcases p23650_3 (m.d 0 2) (by simp) with h23676 | h23676
                          · linarith only [h23676, hlam, p23650_0]
                          · rcases p23650_3 (m.d 1 2) (by simp) with h23678 | h23678
                            · linarith only [h23342, h23678, hlam]
                            · rcases p23650_3 (m.d 2 3) (by simp) with h23680 | h23680
                              · rcases p23650_3 (m.d 2 4) (by simp) with h23681 | h23681
                                · rcases p23650_3 (m.d 2 5) (by simp) with h23682 | h23682
                                  · linarith only [h23351, h23682, hlam]
                                  · linarith only [h22010, h23682, hlam]
                                · linarith only [h23681, hlam, p23650_0]
                              · linarith only [h23680, h4, hlam]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          rcases p23650_3 (m.d 0 2) (by simp) with h23687 | h23687
                          · linarith only [h19744, h23687, hlam]
                          · linarith only [h0, h23687, hlam]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h23349, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h22010, h3, hc12, hc24, hlam, hphi, p23353_1, p23650_1]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          rcases p23650_3 (m.d 0 2) (by simp) with h23693 | h23693
                          · linarith only [h23693, hlam, p23650_0]
                          · rcases p23650_3 (m.d 1 2) (by simp) with h23695 | h23695
                            · linarith only [h23344, h23695, hlam]
                            · rcases p23650_3 (m.d 2 3) (by simp) with h23697 | h23697
                              · rcases p23650_3 (m.d 2 4) (by simp) with h23698 | h23698
                                · rcases p23650_3 (m.d 2 5) (by simp) with h23699 | h23699
                                  · rcases h4bigk with h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c | h23700c
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23348, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23353_1, p23700_1]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h19744, hlam, p23700_1]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      rcases p23700_3 (m.d 0 4) (by simp) with h23704 | h23704
                                      · rcases p23700_3 (m.d 1 4) (by simp) with h23705 | h23705
                                        · linarith only [h2, h23705, hlam]
                                        · linarith only [h23346, h23705, hlam]
                                      · linarith only [h23337, h23704, hlam]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      rcases p23700_3 (m.d 0 4) (by simp) with h23709 | h23709
                                      · rcases p23700_3 (m.d 1 4) (by simp) with h23710 | h23710
                                        · linarith only [h2, h23710, hlam]
                                        · linarith only [h23348, h23710, hlam]
                                      · linarith only [h23709, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h2, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23342, hlam, p23700_1]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h1, h23346, h23352, hc01, hc45, hlam, hphi, ht0b, ht5b, p23700_1]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      rcases p23700_3 (m.d 0 4) (by simp) with h23718 | h23718
                                      · rcases p23700_3 (m.d 1 4) (by simp) with h23719 | h23719
                                        · rcases p23700_3 (m.d 2 4) (by simp) with h23720 | h23720
                                          · rcases p23700_3 (m.d 3 4) (by simp) with h23721 | h23721
                                            · linarith only [h23346, h23721, hlam]
                                            · linarith only [h23352, h23721, hlam]
                                          · linarith only [h23351, h23720, hlam]
                                        · linarith only [h23719, hlam, p23700_0]
                                      · linarith only [h23339, h23718, hlam]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23339, h23349, h3, hc12, hc23, hlam, hphi, p23353_1, p23700_1]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23348, h23349, hc12, hc23, hlam, hphi, p23353_1, p23700_1]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      rcases p23700_3 (m.d 0 4) (by simp) with h23730 | h23730
                                      · linarith only [h19744, h23730, hlam]
                                      · linarith only [h23337, h23730, hlam]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      rcases p23700_3 (m.d 0 4) (by simp) with h23733 | h23733
                                      · linarith only [h19744, h23733, hlam]
                                      · linarith only [h23339, h23733, hlam]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23337, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23346, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23349, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h1, h23346, hc01, hc45, hlam, hphi, ht0b, ht5b, p23700_1]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23339, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23348, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23351, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [h23352, hlam, p23700_0]
                                    · have p23700_0 := h23700c.1
                                      have p23700_1 := h23700c.2.1
                                      have p23700_2 := h23700c.2.2.1
                                      have p23700_3 := h23700c.2.2.2
                                      linarith only [hlam, p23700_0]
                                  · linarith only [h23699, hlam, p23650_0]
                                · linarith only [h19744, h23698, hlam]
                              · linarith only [h23697, h4, hlam]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          rcases p23650_3 (m.d 0 2) (by simp) with h23749 | h23749
                          · linarith only [h22010, h23749, hlam]
                          · linarith only [h0, h23749, hlam]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h23350, hlam, p23650_0]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [h23351, hlam, p23650_1]
                        · have p23650_0 := h23650c.1
                          have p23650_1 := h23650c.2.1
                          have p23650_2 := h23650c.2.2.1
                          have p23650_3 := h23650c.2.2.2
                          linarith only [hlam, p23650_0]
                      · linarith only [h23346, h23348, h23648, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23353_1]
                      · linarith only [h23348, h23648, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23353_1]
                      · linarith only [h23648, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23353_1]
                    · linarith only [h23344, h23647, hlam]
                  · linarith only [h23342, h23646, hlam]
                · linarith only [h23340, h23645, hlam]
            · linarith only [h0, h23642, hlam]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h23347, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [h23348, hlam, p23353_0]
          · have p23353_0 := h23353c.1
            have p23353_1 := h23353c.2.1
            have p23353_2 := h23353c.2.2.1
            have p23353_3 := h23353c.2.2.2
            linarith only [hlam, p23353_0]
        · rcases h1bigk with h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c | h23765c
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            rcases p23765_3 (m.d 0 1) (by simp) with h23767 | h23767
            · rcases p23765_3 (m.d 1 2) (by simp) with h23768 | h23768
              · linarith only [h23768, hlam, p23765_0]
              · rcases p23765_3 (m.d 1 3) (by simp) with h23770 | h23770
                · linarith only [h1, h23770, hlam]
                · linarith only [h23340, h23770, hlam]
            · linarith only [h23767, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23346, h23348, h23352, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23348, h23352, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            rcases p23765_3 (m.d 0 1) (by simp) with h23776 | h23776
            · rcases p23765_3 (m.d 1 2) (by simp) with h23777 | h23777
              · linarith only [h0, h23777, hlam]
              · rcases p23765_3 (m.d 1 3) (by simp) with h23779 | h23779
                · linarith only [h1, h23779, hlam]
                · linarith only [h23347, h23779, hlam]
            · linarith only [h23776, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h0, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23340, hlam, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23342, hlam, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23344, hlam, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h1, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            rcases p23765_3 (m.d 0 1) (by simp) with h23789 | h23789
            · rcases p23765_3 (m.d 1 2) (by simp) with h23790 | h23790
              · linarith only [h23340, h23790, hlam]
              · rcases p23765_3 (m.d 1 3) (by simp) with h23792 | h23792
                · rcases p23765_3 (m.d 1 4) (by simp) with h23793 | h23793
                  · linarith only [h23346, h23793, hlam]
                  · linarith only [h23342, h23793, hlam]
                · linarith only [h23340, h23792, hlam]
            · linarith only [h0, h23789, hlam]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23348, h23352, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h1, h23348, h23352, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h2, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            rcases p23765_3 (m.d 0 1) (by simp) with h23802 | h23802
            · rcases p23765_3 (m.d 1 2) (by simp) with h23803 | h23803
              · linarith only [h23342, h23803, hlam]
              · rcases p23765_3 (m.d 1 3) (by simp) with h23805 | h23805
                · rcases p23765_3 (m.d 1 4) (by simp) with h23806 | h23806
                  · rcases p23765_3 (m.d 1 5) (by simp) with h23807 | h23807
                    · linarith only [h23348, h23807, hlam]
                    · linarith only [h23344, h23807, hlam]
                  · linarith only [h23342, h23806, hlam]
                · linarith only [h23340, h23805, hlam]
            · linarith only [h0, h23802, hlam]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23346, hlam, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h2, h23348, h23352, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23765_1]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h3, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            rcases p23765_3 (m.d 0 1) (by simp) with h23817 | h23817
            · rcases p23765_3 (m.d 1 2) (by simp) with h23818 | h23818
              · linarith only [h23344, h23818, hlam]
              · rcases p23765_3 (m.d 1 3) (by simp) with h23820 | h23820
                · rcases p23765_3 (m.d 1 4) (by simp) with h23821 | h23821
                  · rcases p23765_3 (m.d 1 5) (by simp) with h23822 | h23822
                    · rcases h1emax with h23823 | h23823 | h23823 | h23823 | h23823
                      · linarith only [h23823, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23765_1]
                      · rcases h2bigk with h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c | h23825c
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p23825_1]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h4, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h19744, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h22010, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h0, hlam, p23825_1]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h23340, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h23342, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h23344, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          rcases p23825_3 (m.d 0 2) (by simp) with h23836 | h23836
                          · linarith only [h23836, hlam, p23825_0]
                          · rcases p23825_3 (m.d 1 2) (by simp) with h23838 | h23838
                            · linarith only [h23340, h23838, hlam]
                            · rcases p23825_3 (m.d 2 3) (by simp) with h23840 | h23840
                              · rcases p23825_3 (m.d 2 4) (by simp) with h23841 | h23841
                                · linarith only [h23349, h23841, hlam]
                                · linarith only [h19744, h23841, hlam]
                              · linarith only [h23840, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          rcases p23825_3 (m.d 0 2) (by simp) with h23845 | h23845
                          · linarith only [h23845, h4, hlam]
                          · linarith only [h0, h23845, hlam]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h19744, hc02, hc23, hlam, hphi, p23825_1]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h22010, h3, hc12, hc23, hlam, hphi, p23765_1, p23825_1]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          rcases p23825_3 (m.d 0 2) (by simp) with h23851 | h23851
                          · linarith only [h23851, hlam, p23825_0]
                          · rcases p23825_3 (m.d 1 2) (by simp) with h23853 | h23853
                            · linarith only [h23342, h23853, hlam]
                            · rcases p23825_3 (m.d 2 3) (by simp) with h23855 | h23855
                              · rcases p23825_3 (m.d 2 4) (by simp) with h23856 | h23856
                                · rcases p23825_3 (m.d 2 5) (by simp) with h23857 | h23857
                                  · linarith only [h23351, h23857, hlam]
                                  · linarith only [h22010, h23857, hlam]
                                · linarith only [h23856, hlam, p23825_0]
                              · linarith only [h23855, h4, hlam]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          rcases p23825_3 (m.d 0 2) (by simp) with h23862 | h23862
                          · linarith only [h19744, h23862, hlam]
                          · linarith only [h0, h23862, hlam]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h23349, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h22010, h3, hc12, hc24, hlam, hphi, p23765_1, p23825_1]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          rcases p23825_3 (m.d 0 2) (by simp) with h23868 | h23868
                          · linarith only [h23868, hlam, p23825_0]
                          · rcases p23825_3 (m.d 1 2) (by simp) with h23870 | h23870
                            · linarith only [h23344, h23870, hlam]
                            · rcases p23825_3 (m.d 2 3) (by simp) with h23872 | h23872
                              · rcases p23825_3 (m.d 2 4) (by simp) with h23873 | h23873
                                · rcases p23825_3 (m.d 2 5) (by simp) with h23874 | h23874
                                  · rcases h4bigk with h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c | h23875c
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23348, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23765_1, p23875_1]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h19744, hlam, p23875_1]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      rcases p23875_3 (m.d 0 4) (by simp) with h23879 | h23879
                                      · rcases p23875_3 (m.d 1 4) (by simp) with h23880 | h23880
                                        · linarith only [h2, h23880, hlam]
                                        · linarith only [h23346, h23880, hlam]
                                      · linarith only [h23337, h23879, hlam]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      rcases p23875_3 (m.d 0 4) (by simp) with h23884 | h23884
                                      · rcases p23875_3 (m.d 1 4) (by simp) with h23885 | h23885
                                        · linarith only [h2, h23885, hlam]
                                        · linarith only [h23348, h23885, hlam]
                                      · linarith only [h23884, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h2, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23342, hlam, p23875_1]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      rcases p23875_3 (m.d 0 4) (by simp) with h23892 | h23892
                                      · rcases p23875_3 (m.d 1 4) (by simp) with h23893 | h23893
                                        · rcases p23875_3 (m.d 2 4) (by simp) with h23894 | h23894
                                          · rcases p23875_3 (m.d 3 4) (by simp) with h23895 | h23895
                                            · linarith only [h23346, h23895, hlam]
                                            · rcases p23875_3 (m.d 4 5) (by simp) with h23897 | h23897
                                              · linarith only [h23348, h23897, hlam]
                                              · linarith only [h23352, h23897, hlam]
                                          · linarith only [h23349, h23894, hlam]
                                        · linarith only [h23346, h23893, hlam]
                                      · linarith only [h23337, h23892, hlam]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h1, h23346, h23352, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23875_1]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23339, h23349, h23352, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23875_1]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23348, h23349, h23352, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23875_1]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      rcases p23875_3 (m.d 0 4) (by simp) with h23907 | h23907
                                      · linarith only [h19744, h23907, hlam]
                                      · linarith only [h23337, h23907, hlam]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      rcases p23875_3 (m.d 0 4) (by simp) with h23910 | h23910
                                      · linarith only [h19744, h23910, hlam]
                                      · linarith only [h23339, h23910, hlam]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23337, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23346, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23349, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23352, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23339, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23348, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h23351, hlam, p23875_0]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [h1, h23346, h23348, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23875_1]
                                    · have p23875_0 := h23875c.1
                                      have p23875_1 := h23875c.2.1
                                      have p23875_2 := h23875c.2.2.1
                                      have p23875_3 := h23875c.2.2.2
                                      linarith only [hlam, p23875_0]
                                  · linarith only [h23874, hlam, p23825_0]
                                · linarith only [h19744, h23873, hlam]
                              · linarith only [h23872, h4, hlam]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          rcases p23825_3 (m.d 0 2) (by simp) with h23926 | h23926
                          · linarith only [h22010, h23926, hlam]
                          · linarith only [h0, h23926, hlam]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h23350, hlam, p23825_0]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [h23351, hlam, p23825_1]
                        · have p23825_0 := h23825c.1
                          have p23825_1 := h23825c.2.1
                          have p23825_2 := h23825c.2.2.1
                          have p23825_3 := h23825c.2.2.2
                          linarith only [hlam, p23825_0]
                      · linarith only [h23346, h23348, h23823, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23765_1]
                      · linarith only [h23348, h23823, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23765_1]
                      · linarith only [h23823, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23765_1]
                    · linarith only [h23344, h23822, hlam]
                  · linarith only [h23342, h23821, hlam]
                · linarith only [h23340, h23820, hlam]
            · linarith only [h0, h23817, hlam]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23347, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [h23348, hlam, p23765_0]
          · have p23765_0 := h23765c.1
            have p23765_1 := h23765c.2.1
            have p23765_2 := h23765c.2.2.1
            have p23765_3 := h23765c.2.2.2
            linarith only [hlam, p23765_0]
      · linarith only [h0, h1, h19744, h23346, h23348, h23351, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · linarith only [h23338, h23350, h4, hlam]
  · linarith only [h23337, h23349, h4, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x0_x0 (m : N7Model)
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
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h23946 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h23947 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h23948 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  linarith only [h23346, h23348, h23948, hlam]

end R2N4
