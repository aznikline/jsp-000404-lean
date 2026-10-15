import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8110000 in
set_option maxHeartbeats 8110000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s8 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0 := hg0
  have h6253 := hg6253
  rcases m.htr 0 1 4 (by decide) (by decide) with h7338 | h7338
  · rcases m.htr 0 1 5 (by decide) (by decide) with h7339 | h7339
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7340 | h7340
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7341 | h7341
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7342 | h7342
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7343 | h7343
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7344 | h7344
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7345 | h7345
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7346 | h7346
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7347 | h7347
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7348 | h7348
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7349 | h7349
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7350 | h7350
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7351 | h7351
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7352 | h7352
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7353 | h7353
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7354 | h7354
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7355 | h7355
                                    · rcases h0bigk with h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c | h7356c
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h0, hlam, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h6253, hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h6253, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h6253, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h0, h6253, h7338, h7348, h7351, h7353, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h0, h7343, h7355, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        rcases p7356_3 (m.d 0 1) (by simp) with h7366 | h7366
                                        · linarith only [h0, h7366, hlam]
                                        · linarith only [h7339, h7366, hlam]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7338, h7347, h7352, h7355, hc03, hc45, hlam, hphi, ht0b, ht5b, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7340, hlam, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h6253, h7338, h7346, h7347, h7352, h7355, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        rcases p7356_3 (m.d 0 1) (by simp) with h7373 | h7373
                                        · linarith only [h6253, h7373, hlam]
                                        · linarith only [h7339, h7373, hlam]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7338, hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7341, hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7343, hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h0, h7338, h7339, h7348, h7353, h7355, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7339, hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7342, hlam, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7344, hlam, p7356_0]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [h7345, hlam, p7356_1]
                                      · have p7356_0 := h7356c.1
                                        have p7356_1 := h7356c.2.1
                                        have p7356_2 := h7356c.2.2.1
                                        have p7356_3 := h7356c.2.2.2
                                        linarith only [hlam, p7356_0]
                                    · linarith only [h6253, h7338, h7346, h7347, h7354, h7355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h6253, h7338, h7346, h7351, h7354, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h6253, h7338, h7346, h7350, h7351, h7352, h7353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7389 | h7389
                                · linarith only [h6253, h7338, h7346, h7349, h7352, h7389, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7391 | h7391
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7392 | h7392
                                    · rcases h0bigk with h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h0, hlam, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h6253, hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h6253, h7346, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h6253, h7346, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h0, h6253, h7338, h7350, h7351, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h0, h7338, h7350, h7351, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h0, h7339, h7350, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7338, h7350, h7351, h7389, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7340, hlam, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h0, h7338, h7340, h7350, h7351, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h0, h7339, h7340, h7350, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7338, hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7341, hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7343, hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7339, h7350, h7389, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7339, hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7342, hlam, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7344, hlam, p7393_0]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [h7345, hlam, p7393_1]
                                      · have p7393_0 := h7393c.1
                                        have p7393_1 := h7393c.2.1
                                        have p7393_2 := h7393c.2.2.1
                                        have p7393_3 := h7393c.2.2.2
                                        linarith only [hlam, p7393_0]
                                    · linarith only [h6253, h7338, h7346, h7347, h7391, h7392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h6253, h7338, h7346, h7351, h7391, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7421 | h7421
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7422 | h7422
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7423 | h7423
                                  · linarith only [h7347, h7351, h7423, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7425 | h7425
                                    · linarith only [h7347, h7351, h7421, h7425, hlam]
                                    · rcases h0bigk with h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h0, hlam, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h6253, hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h6253, h7346, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h6253, h7346, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h0, h6253, hc01, hc12, hlam, hphi, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h0, h7345, h7347, h7351, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h0, h7345, h7347, h7351, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7338, h7345, h7347, h7351, h7421, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7340, hlam, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h6253, h7345, h7346, h7347, h7351, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h6253, h7345, h7346, h7347, h7351, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7338, hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7341, hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7343, hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h0, h7338, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7339, hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7342, hlam, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7344, hlam, p7427_0]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [h7345, hlam, p7427_1]
                                      · have p7427_0 := h7427c.1
                                        have p7427_1 := h7427c.2.1
                                        have p7427_2 := h7427c.2.2.1
                                        have p7427_3 := h7427c.2.2.2
                                        linarith only [hlam, p7427_0]
                                · linarith only [h6253, h7339, h7346, h7350, h7421, h7422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h6253, h7338, h7345, h7346, h7349, h7351, h7421, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h6253, h7344, h7350, hlam]
                        · linarith only [h0, h6253, h7340, h7343, h7349, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h7342, h7348, hlam]
                    · linarith only [h0, h7341, h7347, hlam]
                  · linarith only [h0, h7340, h7346, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7460 | h7460
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7461 | h7461
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7462 | h7462
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7463 | h7463
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7464 | h7464
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7465 | h7465
                            · linarith only [h7338, h7345, h7465, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7467 | h7467
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7468 | h7468
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7469 | h7469
                                  · linarith only [h7338, h7345, h7461, h7469, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7471 | h7471
                                    · linarith only [h7338, h7345, h7461, h7467, h7471, hlam]
                                    · rcases h0bigk with h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c | h7473c
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h0, hlam, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h6253, hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h6253, h7460, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h0, h7338, h7345, h7461, h7467, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h0, h6253, h7339, h7461, h7465, h7467, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        rcases p7473_3 (m.d 0 1) (by simp) with h7482 | h7482
                                        · linarith only [h0, h7482, hlam]
                                        · linarith only [h7338, h7482, hlam]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        rcases p7473_3 (m.d 0 1) (by simp) with h7485 | h7485
                                        · linarith only [h0, h7485, hlam]
                                        · linarith only [h7339, h7485, hlam]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7339, h7461, h7465, h7467, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7340, hlam, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        rcases p7473_3 (m.d 0 1) (by simp) with h7491 | h7491
                                        · linarith only [h6253, h7491, hlam]
                                        · linarith only [h7338, h7491, hlam]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        rcases p7473_3 (m.d 0 1) (by simp) with h7494 | h7494
                                        · linarith only [h6253, h7494, hlam]
                                        · linarith only [h7339, h7494, hlam]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7338, hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7341, hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7343, hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7345, hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7339, hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7342, hlam, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h7344, hlam, p7473_0]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [h0, h7338, h7339, h7461, h7467, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7473_1]
                                      · have p7473_0 := h7473c.1
                                        have p7473_1 := h7473c.2.1
                                        have p7473_2 := h7473c.2.2.1
                                        have p7473_3 := h7473c.2.2.2
                                        linarith only [hlam, p7473_0]
                                · linarith only [h6253, h7339, h7460, h7464, h7467, h7468, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7508 | h7508
                                · linarith only [h6253, h7338, h7460, h7463, h7467, h7508, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7510 | h7510
                                  · linarith only [h6253, h7339, h7345, h7460, h7463, h7465, h7467, h7510, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7512 | h7512
                                    · linarith only [h7338, h7345, h7463, h7512, hlam]
                                    · rcases h0bigk with h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c | h7514c
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h0, hlam, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h6253, hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h6253, h7338, h7460, h7463, h7467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h6253, h7460, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h0, h6253, h7338, h7463, h7467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h0, h7338, h7463, h7467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h0, h7338, h7345, h7463, h7467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7338, h7463, h7467, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7340, hlam, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h6253, h7338, h7460, h7463, h7467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h6253, h7338, h7345, h7460, h7463, h7467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7338, hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7341, hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7343, hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7345, hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7339, hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7342, hlam, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7344, hlam, p7514_0]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [h7338, h7463, h7467, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7514_1]
                                      · have p7514_0 := h7514c.1
                                        have p7514_1 := h7514c.2.1
                                        have p7514_2 := h7514c.2.2.1
                                        have p7514_3 := h7514c.2.2.2
                                        linarith only [hlam, p7514_0]
                          · linarith only [h6253, h7344, h7464, hlam]
                        · linarith only [h6253, h7343, h7463, hlam]
                      · linarith only [h0, h7342, h7462, hlam]
                    · linarith only [h0, h7341, h7461, hlam]
                  · linarith only [h0, h7340, h7460, hlam]
              · linarith only [h6253, h7339, h7344, hlam]
            · linarith only [h6253, h7338, h7343, hlam]
          · linarith only [h0, h7339, h7342, hlam]
        · linarith only [h6253, h7338, h7340, h7341, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7549 | h7549
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7550 | h7550
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7551 | h7551
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7552 | h7552
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7553 | h7553
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7554 | h7554
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7555 | h7555
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7556 | h7556
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7557 | h7557
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7558 | h7558
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7559 | h7559
                            · linarith only [h0, h7338, h7340, h7554, h7559, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h7338, h7340, h7553, h7554, h7559, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h7338, h7340, h7552, h7553, h7554, h7558, hc03, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6253, h7551, h7557, hlam]
                      · linarith only [h0, h7338, h7340, h7554, h7555, h7556, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h7340, h7554, h7555, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7566 | h7566
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7567 | h7567
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7568 | h7568
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7569 | h7569
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7570 | h7570
                            · linarith only [h0, h7338, h7554, h7570, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h7338, h7553, h7554, h7566, h7570, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h7339, h7552, h7554, h7569, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6253, h7551, h7568, hlam]
                      · linarith only [h0, h7338, h7550, h7566, h7567, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h6253, h7340, h7549, h7566, hc01, hc13, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7577 | h7577
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7578 | h7578
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7579 | h7579
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7580 | h7580
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7581 | h7581
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7582 | h7582
                            · linarith only [h0, h7338, h7553, h7582, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7584 | h7584
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7585 | h7585
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7586 | h7586
                                  · linarith only [h7340, h7549, h7553, h7577, h7586, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7588 | h7588
                                    · linarith only [h0, h7338, h7340, h7553, h7577, h7578, h7584, h7588, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                                    · rcases h0bigk with h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h0, hlam, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h6253, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h0, h7340, h7577, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h0, h7338, h7340, h7553, h7577, h7578, h7584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7340, h7577, hc01, hc12, hlam, hphi, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7340, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7338, h7340, h7577, h7578, h7584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7338, h7340, h7553, h7577, h7578, h7584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7338, h7340, h7577, h7578, h7584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7340, h7577, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7338, h7340, h7577, h7578, h7584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7338, h7340, h7553, h7577, h7578, h7584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7338, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7549, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7551, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7553, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7339, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7550, hlam, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h7552, hlam, p7590_0]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [h0, h7338, h7339, h7578, h7584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                                      · have p7590_0 := h7590c.1
                                        have p7590_1 := h7590c.2.1
                                        have p7590_2 := h7590c.2.2.1
                                        have p7590_3 := h7590c.2.2.2
                                        linarith only [hlam, p7590_0]
                                · linarith only [h7340, h7552, h7585, hlam]
                              · linarith only [h7340, h7551, h7584, hlam]
                          · linarith only [h6253, h7339, h7552, h7581, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h7340, h7551, h7577, h7580, hlam]
                      · linarith only [h0, h7338, h7550, h7578, h7579, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h7340, h7577, h7578, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7622 | h7622
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7623 | h7623
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7624 | h7624
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7625 | h7625
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7626 | h7626
                            · linarith only [h7338, h7553, h7626, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7628 | h7628
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7629 | h7629
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7630 | h7630
                                  · linarith only [h7338, h7553, h7622, h7630, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7632 | h7632
                                    · linarith only [h7338, h7553, h7622, h7628, h7632, hlam]
                                    · rcases h0bigk with h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c | h7634c
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h0, hlam, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h6253, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h0, h7338, h7577, h7622, h7628, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h0, h7577, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h0, h7577, hc01, hc23, hlam, hphi, ht12, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7340, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h0, h7338, h7577, h7622, h7628, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h0, h7339, h7577, h7622, h7626, h7628, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h6253, h7339, h7577, h7622, h7626, h7628, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h6253, h7577, hc02, hc23, hlam, hphi, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        rcases p7634_3 (m.d 0 1) (by simp) with h7648 | h7648
                                        · linarith only [h6253, h7648, hlam]
                                        · linarith only [h7338, h7648, hlam]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        rcases p7634_3 (m.d 0 1) (by simp) with h7651 | h7651
                                        · linarith only [h6253, h7651, hlam]
                                        · linarith only [h7339, h7651, hlam]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7338, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7549, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7551, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7553, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7339, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7550, hlam, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h7552, hlam, p7634_0]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [h0, h7338, h7339, h7577, h7622, h7628, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7634_1]
                                      · have p7634_0 := h7634c.1
                                        have p7634_1 := h7634c.2.1
                                        have p7634_2 := h7634c.2.2.1
                                        have p7634_3 := h7634c.2.2.2
                                        linarith only [hlam, p7634_0]
                                · linarith only [h0, h7577, h7629, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h7339, h7577, h7622, h7626, h7628, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h6253, h7552, h7625, hlam]
                        · linarith only [h6253, h7551, h7624, hlam]
                      · linarith only [h0, h7339, h7550, h7623, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h7338, h7340, h7549, h7622, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h7339, h7340, h7552, hlam]
            · linarith only [h0, h7338, h7340, h7551, hlam]
          · linarith only [h0, h7339, h7550, hlam]
        · linarith only [h0, h7338, h7549, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7674 | h7674
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7675 | h7675
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7676 | h7676
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7677 | h7677
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7678 | h7678
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7679 | h7679
                · linarith only [h7338, h7339, h7679, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7681 | h7681
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7682 | h7682
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7683 | h7683
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7684 | h7684
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7685 | h7685
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7686 | h7686
                            · linarith only [h7338, h7339, h7679, h7686, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7688 | h7688
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7689 | h7689
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7690 | h7690
                                  · linarith only [h7338, h7339, h7682, h7686, h7690, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7692 | h7692
                                    · linarith only [h7339, h7674, h7686, h7688, h7692, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                    · rcases h0bigk with h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h0, hlam, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h6253, hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7339, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7339, hlam, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h0, h7674, h7689, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        rcases p7694_3 (m.d 0 1) (by simp) with h7703 | h7703
                                        · linarith only [h0, h7703, hlam]
                                        · linarith only [h7338, h7703, hlam]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h0, h7338, h7339, h7682, h7688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7338, h7682, h7688, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7674, hlam, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        rcases p7694_3 (m.d 0 1) (by simp) with h7710 | h7710
                                        · linarith only [h6253, h7710, hlam]
                                        · linarith only [h7338, h7710, hlam]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7338, h7339, h7682, h7688, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7338, hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7675, hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7677, hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7679, hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7338, h7682, h7688, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7676, hlam, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7678, hlam, p7694_0]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [h7338, h7339, h7682, h7686, h7688, hc34, hc45, hlam, hphi, p7694_1]
                                      · have p7694_0 := h7694c.1
                                        have p7694_1 := h7694c.2.1
                                        have p7694_2 := h7694c.2.2.1
                                        have p7694_3 := h7694c.2.2.2
                                        linarith only [hlam, p7694_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7724 | h7724
                                  · linarith only [h7338, h7339, h7682, h7686, h7724, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7726 | h7726
                                    · linarith only [h0, h7339, h7674, h7678, h7686, h7688, h7689, h7726, hc01, hc12, hlam, hphi]
                                    · rcases h0bigk with h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c | h7728c
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h0, hlam, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h6253, hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7339, hlam, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h0, h7678, h7689, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        rcases p7728_3 (m.d 0 1) (by simp) with h7737 | h7737
                                        · linarith only [h0, h7737, hlam]
                                        · linarith only [h7338, h7737, hlam]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h0, h7678, h7688, h7689, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7338, h7682, h7688, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7674, hlam, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        rcases p7728_3 (m.d 0 1) (by simp) with h7744 | h7744
                                        · linarith only [h6253, h7744, hlam]
                                        · linarith only [h7338, h7744, hlam]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h6253, h7678, h7681, h7688, h7689, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7338, hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7675, hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7677, hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7679, hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7338, h7682, h7688, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7676, hlam, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7678, hlam, p7728_0]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [h7338, h7339, h7682, h7686, h7688, hc34, hc45, hlam, hphi, p7728_1]
                                      · have p7728_0 := h7728c.1
                                        have p7728_1 := h7728c.2.1
                                        have p7728_2 := h7728c.2.2.1
                                        have p7728_3 := h7728c.2.2.2
                                        linarith only [hlam, p7728_0]
                              · linarith only [h7338, h7339, h7684, h7686, h7688, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h6253, h7678, h7685, hlam]
                        · linarith only [h6253, h7677, h7684, hlam]
                      · linarith only [h0, h7674, h7676, h7678, h7683, hlam]
                    · linarith only [h0, h7675, h7682, hlam]
                  · linarith only [h0, h7674, h7681, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7764 | h7764
                · linarith only [h6253, h7338, h7678, h7764, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7766 | h7766
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7767 | h7767
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7768 | h7768
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7769 | h7769
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7770 | h7770
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7771 | h7771
                            · linarith only [h6253, h7338, h7678, h7764, h7766, h7770, h7771, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7773 | h7773
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7774 | h7774
                                · linarith only [h6253, h7338, h7674, h7678, h7774, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7776 | h7776
                                  · linarith only [h6253, h7338, h7678, h7767, h7770, h7771, h7776, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7778 | h7778
                                    · linarith only [h6253, h7338, h7678, h7767, h7770, h7771, h7773, h7778, hlam]
                                    · rcases h0bigk with h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c | h7780c
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h0, hlam, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h6253, hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h6253, h7338, h7678, h7767, h7770, h7773, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7339, hlam, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h0, h6253, h7338, h7767, h7773, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        rcases p7780_3 (m.d 0 1) (by simp) with h7789 | h7789
                                        · linarith only [h0, h7789, hlam]
                                        · linarith only [h7338, h7789, hlam]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h0, h6253, h7338, h7678, h7767, h7773, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7338, h7767, h7773, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7674, hlam, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7338, h7678, h7766, h7767, h7770, h7773, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7678, hlam, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7338, hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7675, hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7677, hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7764, hlam, p7780_0]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7338, h7767, h7773, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7676, hlam, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7678, h7766, h7770, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [h7338, h7678, h7766, h7767, h7770, h7773, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7780_1]
                                      · have p7780_0 := h7780c.1
                                        have p7780_1 := h7780c.2.1
                                        have p7780_2 := h7780c.2.2.1
                                        have p7780_3 := h7780c.2.2.2
                                        linarith only [hlam, p7780_0]
                              · linarith only [h7677, h7678, h7766, h7770, h7773, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7809 | h7809
                            · linarith only [h6253, h7338, h7770, h7809, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7811 | h7811
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7812 | h7812
                                · linarith only [h6253, h7770, h7812, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7814 | h7814
                                  · linarith only [h6253, h7338, h7767, h7770, h7809, h7814, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7816 | h7816
                                    · linarith only [h6253, h7677, h7770, h7809, h7816, hlam]
                                    · linarith only [h6253, h7338, h7770, h7816, hc14, hc45, hlam, hphi]
                              · linarith only [h6253, h7677, h7770, h7811, hc23, hc35, hlam, hphi]
                        · linarith only [h6253, h7338, h7677, h7769, hlam]
                      · linarith only [h0, h7676, h7768, hlam]
                    · linarith only [h0, h7675, h7767, hlam]
                  · linarith only [h0, h7674, h7766, hlam]
            · linarith only [h6253, h7338, h7677, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7825 | h7825
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7826 | h7826
              · linarith only [h7674, h7676, h7826, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7828 | h7828
                · linarith only [h6253, h7338, h7674, h7676, h7828, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7830 | h7830
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7831 | h7831
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7832 | h7832
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7833 | h7833
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7834 | h7834
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7835 | h7835
                            · linarith only [h6253, h7338, h7826, h7828, h7834, h7835, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7837 | h7837
                              · linarith only [h7674, h7676, h7832, h7837, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7674, h7676, h7825, h7832, h7837, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7840 | h7840
                            · linarith only [h6253, h7338, h7674, h7676, h7832, h7840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7842 | h7842
                              · linarith only [h7674, h7676, h7832, h7842, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7674, h7676, h7825, h7832, h7842, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h6253, h7338, h7825, h7833, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7846 | h7846
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7847 | h7847
                          · linarith only [h6253, h7338, h7826, h7830, h7831, h7832, h7847, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7849 | h7849
                            · linarith only [h0, h7338, h7832, h7849, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7851 | h7851
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7852 | h7852
                                · linarith only [h6253, h7338, h7831, h7847, h7851, h7852, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7854 | h7854
                                  · linarith only [h6253, h7338, h7830, h7831, h7832, h7849, h7852, h7854, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · linarith only [h6253, h7338, h7830, h7831, h7832, h7851, h7854, hc34, hc45, hlam, hphi]
                              · linarith only [h7825, h7826, h7851, hc23, hc35, hlam, hphi]
                        · linarith only [h6253, h7825, h7826, h7846, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h7675, h7676, h7831, hc12, hc25, hlam, hphi]
                  · linarith only [h0, h7674, h7830, hlam]
            · linarith only [h6253, h7338, h7825, hlam]
        · linarith only [h0, h7338, h7675, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7863 | h7863
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7864 | h7864
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7865 | h7865
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7866 | h7866
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7867 | h7867
                · linarith only [h7338, h7339, h7867, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7869 | h7869
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7870 | h7870
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7871 | h7871
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7872 | h7872
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7873 | h7873
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7874 | h7874
                            · linarith only [h7338, h7339, h7674, h7864, h7867, h7869, h7874, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7876 | h7876
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7877 | h7877
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7878 | h7878
                                  · linarith only [h7338, h7339, h7674, h7864, h7869, h7870, h7874, h7878, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7880 | h7880
                                    · linarith only [h7338, h7339, h7870, h7874, h7876, h7880, hlam]
                                    · rcases h0bigk with h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c | h7882c
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h0, hlam, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h6253, hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7339, h7674, h7864, h7869, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7339, hlam, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7674, h7869, hc01, hc12, hlam, hphi, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7674, hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7338, h7674, h7869, h7870, h7876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7674, h7869, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7338, h7870, h7876, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7674, h7869, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7338, h7674, h7869, h7870, h7876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7338, h7339, h7674, h7869, h7870, h7876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7338, hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7863, hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7865, hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7867, hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7338, h7864, h7870, h7876, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7864, hlam, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7866, hlam, p7882_0]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [h7338, h7674, h7864, h7869, h7870, h7876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7882_1]
                                      · have p7882_0 := h7882c.1
                                        have p7882_1 := h7882c.2.1
                                        have p7882_2 := h7882c.2.2.1
                                        have p7882_3 := h7882c.2.2.2
                                        linarith only [hlam, p7882_0]
                                · linarith only [h7674, h7866, h7877, hlam]
                              · linarith only [h7674, h7865, h7876, hlam]
                          · linarith only [h7674, h7864, h7866, h7869, h7873, hlam]
                        · linarith only [h7674, h7865, h7869, h7872, hlam]
                      · linarith only [h7338, h7339, h7674, h7864, h7869, h7870, h7871, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h7338, h7339, h7674, h7864, h7869, h7870, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7914 | h7914
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7915 | h7915
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7916 | h7916
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7917 | h7917
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7918 | h7918
                            · linarith only [h7338, h7339, h7869, h7915, h7918, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7920 | h7920
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7921 | h7921
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7922 | h7922
                                  · linarith only [h7338, h7339, h7914, h7918, h7922, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7924 | h7924
                                    · linarith only [h7338, h7339, h7914, h7918, h7920, h7924, hlam]
                                    · rcases h0bigk with h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c | h7926c
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h0, hlam, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h6253, hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7338, h7339, h7869, h7914, h7915, h7920, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7339, hlam, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h0, h7869, hc01, hc23, hlam, hphi, ht12, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7674, hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h0, h7338, h7869, h7914, h7920, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h0, h7869, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h6253, h7338, h7869, h7914, h7920, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h6253, h7869, hc02, hc23, hlam, hphi, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        rcases p7926_3 (m.d 0 1) (by simp) with h7940 | h7940
                                        · linarith only [h6253, h7940, hlam]
                                        · linarith only [h7338, h7940, hlam]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h6253, h7338, h7339, h7869, h7914, h7920, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7338, hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7863, hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7865, hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7867, hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7338, h7864, h7914, h7920, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7864, hlam, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h7866, hlam, p7926_0]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [h0, h7338, h7864, h7869, h7914, h7920, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7926_1]
                                      · have p7926_0 := h7926c.1
                                        have p7926_1 := h7926c.2.1
                                        have p7926_2 := h7926c.2.2.1
                                        have p7926_3 := h7926c.2.2.2
                                        linarith only [hlam, p7926_0]
                                · linarith only [h0, h7338, h7869, h7914, h7920, h7921, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h7338, h7339, h7869, h7914, h7915, h7920, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h6253, h7338, h7864, h7866, h7869, h7914, h7917, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h6253, h7865, h7916, hlam]
                      · linarith only [h0, h7338, h7864, h7914, h7915, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7863, h7914, hlam]
              · linarith only [h7674, h7864, h7866, hlam]
            · linarith only [h0, h7338, h7674, h7865, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7962 | h7962
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7963 | h7963
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7964 | h7964
                · linarith only [h0, h7338, h7864, h7964, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7966 | h7966
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7967 | h7967
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7968 | h7968
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7969 | h7969
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7970 | h7970
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7971 | h7971
                            · linarith only [h0, h7338, h7674, h7964, h7966, h7971, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7973 | h7973
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7974 | h7974
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7975 | h7975
                                  · linarith only [h0, h7338, h7864, h7966, h7967, h7971, h7974, h7975, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7977 | h7977
                                    · linarith only [h0, h7338, h7864, h7967, h7968, h7971, h7973, h7977, hlam]
                                    · rcases h0bigk with h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h0, hlam, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h6253, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h0, h7864, h7966, h7974, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7339, hlam, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7864, h7966, h7974, hc01, hc12, hlam, hphi, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7674, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7338, h7864, h7966, h7967, h7973, h7974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7864, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7338, h7967, h7973, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7674, h7966, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7338, h7674, h7966, h7967, h7973, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h0, h7338, h7674, h7864, h7966, h7967, h7973, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7338, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7863, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7962, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7964, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7338, h7967, h7973, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h0, h7338, h7864, h7966, h7967, h7973, h7974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7963, hlam, p7979_0]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [h7338, h7864, h7966, h7967, h7973, h7974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7979_1]
                                      · have p7979_0 := h7979c.1
                                        have p7979_1 := h7979c.2.1
                                        have p7979_2 := h7979c.2.2.1
                                        have p7979_3 := h7979c.2.2.2
                                        linarith only [hlam, p7979_0]
                                · linarith only [h7674, h7963, h7974, hlam]
                              · linarith only [h0, h7338, h7674, h7962, h7967, h7973, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h6253, h7963, h7970, hlam]
                        · linarith only [h7674, h7962, h7966, h7969, hlam]
                      · linarith only [h0, h7338, h7674, h7966, h7967, h7968, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h7338, h7674, h7966, h7967, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8011 | h8011
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8012 | h8012
                      · linarith only [h0, h7338, h7864, h7966, h8011, h8012, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8014 | h8014
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h8015 | h8015
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8016 | h8016
                            · linarith only [h0, h7338, h7964, h7966, h8016, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8018 | h8018
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8019 | h8019
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h8020 | h8020
                                  · linarith only [h0, h7338, h8011, h8012, h8016, h8019, h8020, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h7338, h8011, h8012, h8018, h8020, hc34, hc45, hlam, hphi]
                                · linarith only [h6253, h7963, h7966, h8019, hlam]
                              · linarith only [h6253, h7338, h7962, h7966, h8018, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h6253, h7963, h8015, hlam]
                        · linarith only [h6253, h7962, h8014, hlam]
                    · linarith only [h0, h7338, h7863, h8011, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8028 | h8028
                · linarith only [h0, h7338, h7674, h7963, h8028, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8030 | h8030
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8031 | h8031
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8032 | h8032
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8033 | h8033
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h8034 | h8034
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8035 | h8035
                            · linarith only [h0, h7338, h7674, h7963, h8028, h8034, h8035, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8037 | h8037
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8038 | h8038
                                · linarith only [h0, h7674, h7963, h8030, h8038, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h7338, h7674, h8030, h8031, h8034, h8037, h8038, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h7338, h7674, h7962, h7963, h8037, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8042 | h8042
                            · linarith only [h6253, h7338, h8034, h8042, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8044 | h8044
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8045 | h8045
                                · linarith only [h8030, h8034, h8045, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h8047 | h8047
                                  · linarith only [h0, h7338, h7674, h7864, h8030, h8031, h8032, h8034, h8042, h8047, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8049 | h8049
                                    · linarith only [h0, h7338, h7674, h7864, h7963, h8030, h8031, h8032, h8034, h8042, h8044, h8049, hc03, hc35, hlam, hphi]
                                    · linarith only [h6253, h7338, h8031, h8034, h8044, h8049, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h7338, h7674, h7962, h8031, h8044, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h6253, h7338, h7962, h8033, hlam]
                      · linarith only [h0, h7338, h7674, h8030, h8031, h8032, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h7338, h7674, h8030, h8031, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8056 | h8056
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8057 | h8057
                      · linarith only [h0, h7338, h7864, h8030, h8056, h8057, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8059 | h8059
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h8060 | h8060
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8061 | h8061
                            · linarith only [h0, h7338, h8030, h8061, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8063 | h8063
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8064 | h8064
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h8065 | h8065
                                  · linarith only [h0, h7338, h7674, h7963, h8030, h8056, h8060, h8061, h8065, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h7338, h8056, h8057, h8063, h8065, hc34, hc45, hlam, hphi]
                                · linarith only [h8030, h8060, h8064, hlam]
                              · linarith only [h0, h7338, h7674, h7963, h8030, h8056, h8060, h8063, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8070 | h8070
                            · linarith only [h0, h7338, h8030, h8060, h8070, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8072 | h8072
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8073 | h8073
                                · linarith only [h0, h7338, h8030, h8056, h8060, h8072, h8073, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h7338, h8030, h8056, h8072, h8073, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h7338, h8030, h8056, h8072, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h7338, h7962, h8030, h8056, h8059, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7863, h8056, hlam]
            · linarith only [h6253, h7338, h7962, hlam]
        · linarith only [h0, h7338, h7863, hlam]
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s9 m hb0 hb1 hb3 hb4 h0 h6253 h7338

end R2N4
