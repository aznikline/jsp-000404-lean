import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S29
import Jsp000404.R1LeavesN7_2S30
import Jsp000404.R1LeavesN7_2S31

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h21506 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h21783 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h22297 | h22297
  · rcases h0bigk with h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c | h22298c
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h0, hlam, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h14396, hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h16915, hlam, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h18815, hlam, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      rcases p22298_3 (m.d 0 1) (by simp) with h22304 | h22304
      · linarith only [h0, h22304, hlam]
      · rcases p22298_3 (m.d 0 2) (by simp) with h22306 | h22306
        · rcases p22298_3 (m.d 0 3) (by simp) with h22307 | h22307
          · linarith only [h20408, h22307, hlam]
          · linarith only [h14396, h22307, hlam]
        · linarith only [h0, h22306, hlam]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h0, h20411, h20413, h20420, h21783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h0, h20413, h20420, h21783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      rcases p22298_3 (m.d 0 1) (by simp) with h22314 | h22314
      · linarith only [h0, h22314, hlam]
      · rcases p22298_3 (m.d 0 2) (by simp) with h22316 | h22316
        · rcases p22298_3 (m.d 0 3) (by simp) with h22317 | h22317
          · linarith only [h20408, h22317, hlam]
          · linarith only [h20412, h22317, hlam]
        · linarith only [h20410, h22316, hlam]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      rcases p22298_3 (m.d 0 1) (by simp) with h22321 | h22321
      · linarith only [h14396, h22321, hlam]
      · rcases p22298_3 (m.d 0 2) (by simp) with h22323 | h22323
        · rcases p22298_3 (m.d 0 3) (by simp) with h22324 | h22324
          · rcases p22298_3 (m.d 0 4) (by simp) with h22325 | h22325
            · linarith only [h20411, h22325, hlam]
            · linarith only [h16915, h22325, hlam]
          · linarith only [h14396, h22324, hlam]
        · linarith only [h0, h22323, hlam]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h20408, hlam, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h20411, h20420, h21783, h22297, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      rcases p22298_3 (m.d 0 1) (by simp) with h22333 | h22333
      · linarith only [h14396, h22333, hlam]
      · rcases p22298_3 (m.d 0 2) (by simp) with h22335 | h22335
        · rcases p22298_3 (m.d 0 3) (by simp) with h22336 | h22336
          · rcases p22298_3 (m.d 0 4) (by simp) with h22337 | h22337
            · linarith only [h20411, h22337, hlam]
            · linarith only [h20413, h22337, hlam]
          · linarith only [h20412, h22336, hlam]
        · linarith only [h20410, h22335, hlam]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      rcases p22298_3 (m.d 0 1) (by simp) with h22342 | h22342
      · linarith only [h16915, h22342, hlam]
      · rcases p22298_3 (m.d 0 2) (by simp) with h22344 | h22344
        · rcases p22298_3 (m.d 0 3) (by simp) with h22345 | h22345
          · rcases p22298_3 (m.d 0 4) (by simp) with h22346 | h22346
            · rcases p22298_3 (m.d 0 5) (by simp) with h22347 | h22347
              · linarith only [h20413, h22347, hlam]
              · linarith only [h18815, h22347, hlam]
            · linarith only [h16915, h22346, hlam]
          · linarith only [h14396, h22345, hlam]
        · linarith only [h0, h22344, hlam]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h20409, hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h20411, hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      rcases p22298_3 (m.d 0 1) (by simp) with h22356 | h22356
      · linarith only [h16915, h22356, hlam]
      · rcases p22298_3 (m.d 0 2) (by simp) with h22358 | h22358
        · rcases p22298_3 (m.d 0 3) (by simp) with h22359 | h22359
          · rcases p22298_3 (m.d 0 4) (by simp) with h22360 | h22360
            · rcases p22298_3 (m.d 0 5) (by simp) with h22361 | h22361
              · linarith only [h20413, h22361, hlam]
              · rcases h2bigk with h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c | h22363c
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h0, hlam, p22363_1]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20408, h20411, h20420, h21783, h22297, hlam, p22363_2]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20408, h20411, h21783, h22297, hlam, p22363_2]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  rcases p22363_3 (m.d 0 2) (by simp) with h22368 | h22368
                  · rcases p22363_3 (m.d 1 2) (by simp) with h22369 | h22369
                    · rcases p22363_3 (m.d 2 3) (by simp) with h22370 | h22370
                      · linarith only [h20408, h22370, hlam]
                      · rcases p22363_3 (m.d 2 4) (by simp) with h22372 | h22372
                        · linarith only [h20409, h22372, hlam]
                        · rcases p22363_3 (m.d 2 5) (by simp) with h22374 | h22374
                          · linarith only [h22374, hlam, p22363_0]
                          · rcases h3bigk with h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c | h22376c
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h14396, hlam, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              rcases p22376_3 (m.d 0 3) (by simp) with h22379 | h22379
                              · rcases p22376_3 (m.d 1 3) (by simp) with h22380 | h22380
                                · rcases p22376_3 (m.d 2 3) (by simp) with h22381 | h22381
                                  · linarith only [h20408, h22381, hlam]
                                  · rcases p22376_3 (m.d 3 4) (by simp) with h22383 | h22383
                                    · linarith only [h20411, h22383, hlam]
                                    · linarith only [h20420, h22383, hlam]
                                · linarith only [h20414, h22380, hlam]
                              · linarith only [h20408, h22379, hlam]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20408, h20420, h21783, h22297, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h0, h20408, h20420, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              rcases p22376_3 (m.d 0 3) (by simp) with h22392 | h22392
                              · linarith only [h14396, h22392, hlam]
                              · linarith only [h20408, h22392, hlam]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20414, h20420, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20414, h20420, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20408, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20414, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20420, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h21506, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20411, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20417, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [hc23, hc34, hlam, hphi, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20411, h20420, h21783, h22297, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20412, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20418, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h20412, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22298_1, p22376_1]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [h22297, hlam, p22376_0]
                            · have p22376_0 := h22376c.1
                              have p22376_1 := h22376c.2.1
                              have p22376_2 := h22376c.2.2.1
                              have p22376_3 := h22376c.2.2.2
                              linarith only [hlam, p22376_0]
                    · linarith only [h20416, h22369, hlam]
                  · linarith only [h22368, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20409, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p22298_1, p22363_1]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h0, h20408, h20411, h20413, h20420, h21783, hlam, p22298_1, p22363_2]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h0, h20408, h20411, h20413, h21783, hlam, p22298_1, p22363_2]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  rcases p22363_3 (m.d 0 2) (by simp) with h22418 | h22418
                  · linarith only [h0, h22418, hlam]
                  · linarith only [h20410, h22418, hlam]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20408, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20414, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20420, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h21506, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20409, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20415, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h0, h20408, h20411, h20412, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22298_1, p22363_1]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h21783, hlam, p22363_1]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20410, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h20416, hlam, p22363_0]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h0, h20408, h20411, h20412, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22298_1, p22363_1]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [h0, h20408, h20411, h20412, h21783, h22297, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p22298_1, p22363_1]
                · have p22363_0 := h22363c.1
                  have p22363_1 := h22363c.2.1
                  have p22363_2 := h22363c.2.2.1
                  have p22363_3 := h22363c.2.2.2
                  linarith only [hlam, p22363_0]
            · linarith only [h20413, h22360, hlam]
          · linarith only [h20412, h22359, hlam]
        · linarith only [h20410, h22358, hlam]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      rcases p22298_3 (m.d 0 1) (by simp) with h22439 | h22439
      · linarith only [h18815, h22439, hlam]
      · rcases p22298_3 (m.d 0 2) (by simp) with h22441 | h22441
        · rcases p22298_3 (m.d 0 3) (by simp) with h22442 | h22442
          · rcases p22298_3 (m.d 0 4) (by simp) with h22443 | h22443
            · rcases p22298_3 (m.d 0 5) (by simp) with h22444 | h22444
              · rcases h2bigk with h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c | h22445c
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h0, hlam, p22445_1]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20408, h20411, h20420, h21783, h22297, hlam, p22445_2]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20408, h20411, h21783, h22297, hlam, p22445_2]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  rcases p22445_3 (m.d 0 2) (by simp) with h22450 | h22450
                  · rcases p22445_3 (m.d 1 2) (by simp) with h22451 | h22451
                    · rcases p22445_3 (m.d 2 3) (by simp) with h22452 | h22452
                      · linarith only [h20408, h22452, hlam]
                      · rcases p22445_3 (m.d 2 4) (by simp) with h22454 | h22454
                        · linarith only [h20409, h22454, hlam]
                        · rcases p22445_3 (m.d 2 5) (by simp) with h22456 | h22456
                          · linarith only [h22456, hlam, p22445_0]
                          · rcases h3bigk with h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c | h22458c
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h14396, hlam, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              rcases p22458_3 (m.d 0 3) (by simp) with h22461 | h22461
                              · rcases p22458_3 (m.d 1 3) (by simp) with h22462 | h22462
                                · rcases p22458_3 (m.d 2 3) (by simp) with h22463 | h22463
                                  · linarith only [h20408, h22463, hlam]
                                  · rcases p22458_3 (m.d 3 4) (by simp) with h22465 | h22465
                                    · linarith only [h20411, h22465, hlam]
                                    · linarith only [h20420, h22465, hlam]
                                · linarith only [h20414, h22462, hlam]
                              · linarith only [h20408, h22461, hlam]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h0, h20408, h20420, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h0, h20408, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              rcases p22458_3 (m.d 0 3) (by simp) with h22474 | h22474
                              · linarith only [h14396, h22474, hlam]
                              · linarith only [h20408, h22474, hlam]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20414, h20420, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20414, h20420, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20408, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20414, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20420, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h21506, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20411, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20417, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20411, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h14396, h20411, h20414, h20420, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20412, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h20418, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [hc23, hc35, hlam, hphi, p22458_1]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [h22297, hlam, p22458_0]
                            · have p22458_0 := h22458c.1
                              have p22458_1 := h22458c.2.1
                              have p22458_2 := h22458c.2.2.1
                              have p22458_3 := h22458c.2.2.2
                              linarith only [hlam, p22458_0]
                    · linarith only [h20416, h22451, hlam]
                  · linarith only [h22450, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20409, h20413, hc01, hc12, hlam, hphi, p22298_1, p22445_1]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h0, h20408, h20411, h20420, h21783, h22297, hlam, p22445_2]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h0, h20408, h20411, h21783, h22297, hlam, p22445_2]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  rcases p22445_3 (m.d 0 2) (by simp) with h22500 | h22500
                  · linarith only [h0, h22500, hlam]
                  · linarith only [h20410, h22500, hlam]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20408, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20414, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20420, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h21506, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20409, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20415, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20408, h20411, h21783, h22297, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22445_1]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h21783, hlam, p22445_1]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20410, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h20416, hlam, p22445_0]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h0, h20408, h20411, h21783, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22445_1]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [h0, h20408, h20411, h21783, h22297, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p22445_1]
                · have p22445_0 := h22445c.1
                  have p22445_1 := h22445c.2.1
                  have p22445_2 := h22445c.2.2.1
                  have p22445_3 := h22445c.2.2.2
                  linarith only [hlam, p22445_0]
              · linarith only [h18815, h22444, hlam]
            · linarith only [h16915, h22443, hlam]
          · linarith only [h14396, h22442, hlam]
        · linarith only [h0, h22441, hlam]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h20410, hlam, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h20412, hlam, p22298_0]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [h20413, hlam, p22298_1]
    · have p22298_0 := h22298c.1
      have p22298_1 := h22298c.2.1
      have p22298_2 := h22298c.2.2.1
      have p22298_3 := h22298c.2.2.2
      linarith only [hlam, p22298_0]
  · rcases h0bigk with h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c | h22526c
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h0, hlam, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h14396, hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h16915, hlam, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h18815, hlam, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      rcases p22526_3 (m.d 0 1) (by simp) with h22532 | h22532
      · linarith only [h0, h22532, hlam]
      · rcases p22526_3 (m.d 0 2) (by simp) with h22534 | h22534
        · rcases p22526_3 (m.d 0 3) (by simp) with h22535 | h22535
          · linarith only [h20408, h22535, hlam]
          · linarith only [h14396, h22535, hlam]
        · linarith only [h0, h22534, hlam]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h0, h20411, h20413, h22297, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h0, h20413, h22297, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h0, h20413, h20420, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      rcases p22526_3 (m.d 0 1) (by simp) with h22543 | h22543
      · linarith only [h14396, h22543, hlam]
      · rcases p22526_3 (m.d 0 2) (by simp) with h22545 | h22545
        · rcases p22526_3 (m.d 0 3) (by simp) with h22546 | h22546
          · rcases p22526_3 (m.d 0 4) (by simp) with h22547 | h22547
            · linarith only [h20411, h22547, hlam]
            · linarith only [h16915, h22547, hlam]
          · linarith only [h14396, h22546, hlam]
        · linarith only [h0, h22545, hlam]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20408, hlam, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20413, h20420, h22297, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h14396, h20413, h20414, h20420, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      rcases p22526_3 (m.d 0 1) (by simp) with h22556 | h22556
      · linarith only [h16915, h22556, hlam]
      · rcases p22526_3 (m.d 0 2) (by simp) with h22558 | h22558
        · rcases p22526_3 (m.d 0 3) (by simp) with h22559 | h22559
          · rcases p22526_3 (m.d 0 4) (by simp) with h22560 | h22560
            · rcases p22526_3 (m.d 0 5) (by simp) with h22561 | h22561
              · linarith only [h20413, h22561, hlam]
              · linarith only [h18815, h22561, hlam]
            · linarith only [h16915, h22560, hlam]
          · linarith only [h14396, h22559, hlam]
        · linarith only [h0, h22558, hlam]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20409, hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20411, hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20413, h20420, h22297, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      rcases p22526_3 (m.d 0 1) (by simp) with h22571 | h22571
      · linarith only [h18815, h22571, hlam]
      · rcases p22526_3 (m.d 0 2) (by simp) with h22573 | h22573
        · rcases p22526_3 (m.d 0 3) (by simp) with h22574 | h22574
          · rcases p22526_3 (m.d 0 4) (by simp) with h22575 | h22575
            · rcases p22526_3 (m.d 0 5) (by simp) with h22576 | h22576
              · rcases h2bigk with h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c | h22577c
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h0, hlam, p22577_1]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20408, h20411, h20413, h20420, h22297, hlam, p22577_2]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  rcases p22577_3 (m.d 0 2) (by simp) with h22581 | h22581
                  · rcases p22577_3 (m.d 1 2) (by simp) with h22582 | h22582
                    · rcases p22577_3 (m.d 2 3) (by simp) with h22583 | h22583
                      · linarith only [h20408, h22583, hlam]
                      · rcases p22577_3 (m.d 2 4) (by simp) with h22585 | h22585
                        · linarith only [h22585, hlam, p22577_0]
                        · rcases p22577_3 (m.d 2 5) (by simp) with h22587 | h22587
                          · linarith only [h20410, h22587, hlam]
                          · linarith only [h21783, h22587, hlam]
                    · linarith only [h20415, h22582, hlam]
                  · linarith only [h22581, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  rcases p22577_3 (m.d 0 2) (by simp) with h22592 | h22592
                  · rcases p22577_3 (m.d 1 2) (by simp) with h22593 | h22593
                    · rcases p22577_3 (m.d 2 3) (by simp) with h22594 | h22594
                      · linarith only [h20408, h22594, hlam]
                      · rcases p22577_3 (m.d 2 4) (by simp) with h22596 | h22596
                        · linarith only [h20409, h22596, hlam]
                        · rcases p22577_3 (m.d 2 5) (by simp) with h22598 | h22598
                          · linarith only [h22598, hlam, p22577_0]
                          · rcases h3bigk with h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c | h22600c
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h14396, hlam, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              rcases p22600_3 (m.d 0 3) (by simp) with h22603 | h22603
                              · rcases p22600_3 (m.d 1 3) (by simp) with h22604 | h22604
                                · rcases p22600_3 (m.d 2 3) (by simp) with h22605 | h22605
                                  · linarith only [h20408, h22605, hlam]
                                  · rcases p22600_3 (m.d 3 4) (by simp) with h22607 | h22607
                                    · linarith only [h20411, h22607, hlam]
                                    · linarith only [h20420, h22607, hlam]
                                · linarith only [h20414, h22604, hlam]
                              · linarith only [h20408, h22603, hlam]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20408, h20420, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h0, h20408, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              rcases p22600_3 (m.d 0 3) (by simp) with h22616 | h22616
                              · linarith only [h14396, h22616, hlam]
                              · linarith only [h20408, h22616, hlam]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20414, h20420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20414, h20420, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20408, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20414, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20420, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h21506, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20411, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20417, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20411, h20413, h22297, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h22297, hlam, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20412, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h20418, hlam, p22600_0]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [hc23, hc35, hlam, hphi, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [h14396, h20411, h20413, h20414, h22297, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22600_1]
                            · have p22600_0 := h22600c.1
                              have p22600_1 := h22600c.2.1
                              have p22600_2 := h22600c.2.2.1
                              have p22600_3 := h22600c.2.2.2
                              linarith only [hlam, p22600_0]
                    · linarith only [h20416, h22593, hlam]
                  · linarith only [h22592, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20410, hc01, hc12, hlam, hphi, p22526_1, p22577_1]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h0, h20408, h20411, h20413, h20420, h22297, hlam, p22577_2]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  rcases p22577_3 (m.d 0 2) (by simp) with h22641 | h22641
                  · linarith only [h0, h22641, hlam]
                  · linarith only [h20409, h22641, hlam]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  rcases p22577_3 (m.d 0 2) (by simp) with h22644 | h22644
                  · linarith only [h0, h22644, hlam]
                  · linarith only [h20410, h22644, hlam]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20408, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20414, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20420, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h21506, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20409, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20415, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h0, h20408, h20411, h20413, h20420, h22297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22577_1]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h21783, hlam, p22577_1]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20410, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [h20416, hlam, p22577_0]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  rcases p22577_3 (m.d 0 2) (by simp) with h22659 | h22659
                  · rcases p22577_3 (m.d 1 2) (by simp) with h22660 | h22660
                    · rcases p22577_3 (m.d 2 3) (by simp) with h22661 | h22661
                      · linarith only [h21506, h22661, hlam]
                      · rcases p22577_3 (m.d 2 4) (by simp) with h22663 | h22663
                        · linarith only [h21783, h22663, hlam]
                        · linarith only [h20420, h22663, hlam]
                    · linarith only [h20414, h22660, hlam]
                  · linarith only [h20408, h22659, hlam]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  rcases p22577_3 (m.d 0 2) (by simp) with h22668 | h22668
                  · rcases p22577_3 (m.d 1 2) (by simp) with h22669 | h22669
                    · rcases p22577_3 (m.d 2 3) (by simp) with h22670 | h22670
                      · linarith only [h21506, h22670, hlam]
                      · rcases p22577_3 (m.d 2 4) (by simp) with h22672 | h22672
                        · linarith only [h21783, h22672, hlam]
                        · rcases p22577_3 (m.d 2 5) (by simp) with h22674 | h22674
                          · rcases h3bigk with h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c | h22675c
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h14396, hlam, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              rcases p22675_3 (m.d 0 3) (by simp) with h22678 | h22678
                              · rcases p22675_3 (m.d 1 3) (by simp) with h22679 | h22679
                                · rcases p22675_3 (m.d 2 3) (by simp) with h22680 | h22680
                                  · linarith only [h20408, h22680, hlam]
                                  · rcases p22675_3 (m.d 3 4) (by simp) with h22682 | h22682
                                    · linarith only [h20411, h22682, hlam]
                                    · linarith only [h20420, h22682, hlam]
                                · linarith only [h20414, h22679, hlam]
                              · linarith only [h20408, h22678, hlam]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h0, h20408, h20420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h0, h20408, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20411, h20413, h20414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              rcases p22675_3 (m.d 0 3) (by simp) with h22691 | h22691
                              · linarith only [h14396, h22691, hlam]
                              · linarith only [h20408, h22691, hlam]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20414, h20420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20414, h20420, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22577_1, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20408, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20414, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20420, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h21506, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20411, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20417, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [hc23, hc34, hlam, hphi, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h22297, hlam, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20412, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20418, hlam, p22675_0]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h20411, h20413, h22297, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [h14396, h20411, h20413, h20414, h22297, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22675_1]
                            · have p22675_0 := h22675c.1
                              have p22675_1 := h22675c.2.1
                              have p22675_2 := h22675c.2.2.1
                              have p22675_3 := h22675c.2.2.2
                              linarith only [hlam, p22675_0]
                          · linarith only [h21783, h22674, hlam]
                    · linarith only [h20415, h22669, hlam]
                  · linarith only [h20409, h22668, hlam]
                · have p22577_0 := h22577c.1
                  have p22577_1 := h22577c.2.1
                  have p22577_2 := h22577c.2.2.1
                  have p22577_3 := h22577c.2.2.2
                  linarith only [hlam, p22577_0]
              · linarith only [h18815, h22576, hlam]
            · linarith only [h16915, h22575, hlam]
          · linarith only [h14396, h22574, hlam]
        · linarith only [h0, h22573, hlam]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20410, hlam, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20412, hlam, p22526_0]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [h20413, hlam, p22526_1]
    · have p22526_0 := h22526c.1
      have p22526_1 := h22526c.2.1
      have p22526_2 := h22526c.2.2.1
      have p22526_3 := h22526c.2.2.2
      linarith only [hlam, p22526_0]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h21506 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h21783 | h21783
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h21506 h21783
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h21506 h21783

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h21506 | h21506
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h21506
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420 h21506

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h20420 | h20420
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419 h20420

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  linarith only [h14396, h16915, h20411, h20413, h20414, h20419, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h20419 | h20419
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418 h20419

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  linarith only [h14396, h20412, h20418, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  rcases m.htr 1 3 5 (by decide) (by decide) with h20418 | h20418
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417 h20418

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  linarith only [h14396, h20411, h20417, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h20417 | h20417
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416 h20417

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  linarith only [h0, h20410, h20416, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h20416 | h20416
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415 h20416

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  linarith only [h0, h20409, h20415, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h20415 | h20415
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414 h20415

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x1 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  linarith only [h0, h20408, h20414, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0 (m : N7Model)
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
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h20414 | h20414
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h20414

end R2N4
