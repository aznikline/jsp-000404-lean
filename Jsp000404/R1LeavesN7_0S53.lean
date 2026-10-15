import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S48
import Jsp000404.R1LeavesN7_0S49
import Jsp000404.R1LeavesN7_0S52

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x1 (m : N7Model)
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
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h30177 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h31394 | h31394
  · linarith only [h0, h31394, h4, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h31396 | h31396
    · linarith only [h0, h19744, h31396, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h31398 | h31398
      · linarith only [h0, h22010, h31398, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h31400 | h31400
        · linarith only [h1, h23337, h31400, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h31402 | h31402
          · linarith only [h1, h29475, h31402, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h31404 | h31404
            · linarith only [h2, h30177, h31404, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h31406 | h31406
              · rcases m.htr 2 3 5 (by decide) (by decide) with h31407 | h31407
                · rcases m.htr 2 4 5 (by decide) (by decide) with h31408 | h31408
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h31409 | h31409
                    · linarith only [h2, h30177, h31394, h31400, h31406, h31409, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h23337, h31406, h31408, h31409, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h31412 | h31412
                    · linarith only [h0, h19744, h31408, h31412, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c | h31414c
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        rcases p31414_3 (m.d 0 1) (by simp) with h31416 | h31416
                        · rcases p31414_3 (m.d 1 2) (by simp) with h31417 | h31417
                          · linarith only [h31417, hlam, p31414_0]
                          · rcases p31414_3 (m.d 1 3) (by simp) with h31419 | h31419
                            · linarith only [h1, h31419, hlam]
                            · linarith only [h31394, h31419, hlam]
                        · linarith only [h31416, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        rcases p31414_3 (m.d 0 1) (by simp) with h31423 | h31423
                        · rcases p31414_3 (m.d 1 2) (by simp) with h31424 | h31424
                          · linarith only [h0, h31424, hlam]
                          · rcases p31414_3 (m.d 1 3) (by simp) with h31426 | h31426
                            · linarith only [h31426, hlam, p31414_0]
                            · rcases p31414_3 (m.d 1 4) (by simp) with h31428 | h31428
                              · linarith only [h2, h31428, hlam]
                              · linarith only [h31400, h31428, hlam]
                        · linarith only [h31423, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        rcases p31414_3 (m.d 0 1) (by simp) with h31432 | h31432
                        · rcases p31414_3 (m.d 1 2) (by simp) with h31433 | h31433
                          · linarith only [h0, h31433, hlam]
                          · rcases p31414_3 (m.d 1 3) (by simp) with h31435 | h31435
                            · linarith only [h1, h31435, hlam]
                            · rcases p31414_3 (m.d 1 4) (by simp) with h31437 | h31437
                              · linarith only [h31437, hlam, p31414_0]
                              · rcases p31414_3 (m.d 1 5) (by simp) with h31439 | h31439
                                · linarith only [h3, h31439, hlam]
                                · linarith only [h31404, h31439, hlam]
                        · linarith only [h31432, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        rcases p31414_3 (m.d 0 1) (by simp) with h31443 | h31443
                        · rcases p31414_3 (m.d 1 2) (by simp) with h31444 | h31444
                          · linarith only [h0, h31444, hlam]
                          · rcases p31414_3 (m.d 1 3) (by simp) with h31446 | h31446
                            · linarith only [h1, h31446, hlam]
                            · rcases p31414_3 (m.d 1 4) (by simp) with h31448 | h31448
                              · linarith only [h2, h31448, hlam]
                              · rcases p31414_3 (m.d 1 5) (by simp) with h31450 | h31450
                                · linarith only [h31450, hlam, p31414_0]
                                · rcases h1emax with h31452 | h31452 | h31452 | h31452 | h31452
                                  · linarith only [h31394, h31400, h31404, h31452, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p31414_1]
                                  · rcases h2bigk with h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c | h31454c
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h23337, h31406, h4, hc12, hc24, hlam, hphi, p31454_1]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h4, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h19744, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h22010, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h0, hlam, p31454_1]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h31394, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h31396, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h31398, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      rcases p31454_3 (m.d 0 2) (by simp) with h31465 | h31465
                                      · linarith only [h31465, hlam, p31454_0]
                                      · rcases p31454_3 (m.d 1 2) (by simp) with h31467 | h31467
                                        · linarith only [h31394, h31467, hlam]
                                        · rcases p31454_3 (m.d 2 3) (by simp) with h31469 | h31469
                                          · rcases p31454_3 (m.d 2 4) (by simp) with h31470 | h31470
                                            · linarith only [h31406, h31470, hlam]
                                            · linarith only [h19744, h31470, hlam]
                                          · linarith only [h31469, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      rcases p31454_3 (m.d 0 2) (by simp) with h31474 | h31474
                                      · linarith only [h31474, h4, hlam]
                                      · linarith only [h0, h31474, hlam]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h19744, hc02, hc23, hlam, hphi, p31454_1]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h0, h22010, hc12, hc23, hlam, hphi, p31454_1]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h0, h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31454_1]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31454_1]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h31406, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h31408, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      rcases p31454_3 (m.d 0 2) (by simp) with h31485 | h31485
                                      · linarith only [h31485, hlam, p31454_0]
                                      · rcases p31454_3 (m.d 1 2) (by simp) with h31487 | h31487
                                        · linarith only [h31398, h31487, hlam]
                                        · rcases p31454_3 (m.d 2 3) (by simp) with h31489 | h31489
                                          · rcases p31454_3 (m.d 2 4) (by simp) with h31490 | h31490
                                            · linarith only [h31408, h31490, hlam]
                                            · linarith only [h19744, h31490, hlam]
                                          · linarith only [h31489, h4, hlam]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      rcases p31454_3 (m.d 0 2) (by simp) with h31494 | h31494
                                      · linarith only [h22010, h31494, hlam]
                                      · linarith only [h0, h31494, hlam]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h31407, hlam, p31454_0]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p31454_1]
                                    · have p31454_0 := h31454c.1
                                      have p31454_1 := h31454c.2.1
                                      have p31454_2 := h31454c.2.2.1
                                      have p31454_3 := h31454c.2.2.2
                                      linarith only [hlam, p31454_0]
                                  · rcases h2bigk with h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c | h31500c
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p31500_1]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h4, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h19744, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h22010, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h0, hlam, p31500_1]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h31394, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h31396, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h31398, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      rcases p31500_3 (m.d 0 2) (by simp) with h31511 | h31511
                                      · linarith only [h31511, hlam, p31500_0]
                                      · rcases p31500_3 (m.d 1 2) (by simp) with h31513 | h31513
                                        · linarith only [h31394, h31513, hlam]
                                        · rcases p31500_3 (m.d 2 3) (by simp) with h31515 | h31515
                                          · rcases p31500_3 (m.d 2 4) (by simp) with h31516 | h31516
                                            · linarith only [h31406, h31516, hlam]
                                            · linarith only [h19744, h31516, hlam]
                                          · linarith only [h31515, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      rcases p31500_3 (m.d 0 2) (by simp) with h31520 | h31520
                                      · linarith only [h31520, h4, hlam]
                                      · linarith only [h0, h31520, hlam]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h1, h23337, h31394, h31406, hc12, hc23, hlam, hphi, p31500_1]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h22010, hc02, hc23, hlam, hphi, p31500_1]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h0, h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31500_1]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31500_1]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h31406, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h31408, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      rcases p31500_3 (m.d 0 2) (by simp) with h31531 | h31531
                                      · linarith only [h31531, hlam, p31500_0]
                                      · rcases p31500_3 (m.d 1 2) (by simp) with h31533 | h31533
                                        · linarith only [h31398, h31533, hlam]
                                        · rcases p31500_3 (m.d 2 3) (by simp) with h31535 | h31535
                                          · rcases p31500_3 (m.d 2 4) (by simp) with h31536 | h31536
                                            · linarith only [h31408, h31536, hlam]
                                            · linarith only [h19744, h31536, hlam]
                                          · linarith only [h31535, h4, hlam]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      rcases p31500_3 (m.d 0 2) (by simp) with h31540 | h31540
                                      · linarith only [h22010, h31540, hlam]
                                      · linarith only [h0, h31540, hlam]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h31407, hlam, p31500_0]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p31500_1]
                                    · have p31500_0 := h31500c.1
                                      have p31500_1 := h31500c.2.1
                                      have p31500_2 := h31500c.2.2.1
                                      have p31500_3 := h31500c.2.2.2
                                      linarith only [hlam, p31500_0]
                                  · rcases h2bigk with h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c | h31546c
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p31546_1]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h4, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h19744, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h22010, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h0, hlam, p31546_1]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h31394, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h31396, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h31398, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      rcases p31546_3 (m.d 0 2) (by simp) with h31557 | h31557
                                      · linarith only [h31557, hlam, p31546_0]
                                      · rcases p31546_3 (m.d 1 2) (by simp) with h31559 | h31559
                                        · linarith only [h31394, h31559, hlam]
                                        · rcases p31546_3 (m.d 2 3) (by simp) with h31561 | h31561
                                          · rcases p31546_3 (m.d 2 4) (by simp) with h31562 | h31562
                                            · linarith only [h31406, h31562, hlam]
                                            · linarith only [h19744, h31562, hlam]
                                          · linarith only [h31561, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      rcases p31546_3 (m.d 0 2) (by simp) with h31566 | h31566
                                      · linarith only [h31566, h4, hlam]
                                      · linarith only [h0, h31566, hlam]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h1, h23337, h31394, h31406, hc12, hc23, hlam, hphi, p31546_1]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h22010, hc02, hc23, hlam, hphi, p31546_1]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h0, h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31546_1]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31546_1]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h31406, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h31408, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      rcases p31546_3 (m.d 0 2) (by simp) with h31577 | h31577
                                      · linarith only [h31577, hlam, p31546_0]
                                      · rcases p31546_3 (m.d 1 2) (by simp) with h31579 | h31579
                                        · linarith only [h31398, h31579, hlam]
                                        · rcases p31546_3 (m.d 2 3) (by simp) with h31581 | h31581
                                          · rcases p31546_3 (m.d 2 4) (by simp) with h31582 | h31582
                                            · linarith only [h31408, h31582, hlam]
                                            · linarith only [h19744, h31582, hlam]
                                          · linarith only [h31581, h4, hlam]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      rcases p31546_3 (m.d 0 2) (by simp) with h31586 | h31586
                                      · linarith only [h22010, h31586, hlam]
                                      · linarith only [h0, h31586, hlam]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h31407, hlam, p31546_0]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p31546_1]
                                    · have p31546_0 := h31546c.1
                                      have p31546_1 := h31546c.2.1
                                      have p31546_2 := h31546c.2.2.1
                                      have p31546_3 := h31546c.2.2.2
                                      linarith only [hlam, p31546_0]
                                  · rcases h2bigk with h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c | h31592c
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p31592_1]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h4, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h19744, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h22010, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h0, hlam, p31592_1]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h31394, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h31396, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h31398, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      rcases p31592_3 (m.d 0 2) (by simp) with h31603 | h31603
                                      · linarith only [h31603, hlam, p31592_0]
                                      · rcases p31592_3 (m.d 1 2) (by simp) with h31605 | h31605
                                        · linarith only [h31394, h31605, hlam]
                                        · rcases p31592_3 (m.d 2 3) (by simp) with h31607 | h31607
                                          · rcases p31592_3 (m.d 2 4) (by simp) with h31608 | h31608
                                            · linarith only [h31406, h31608, hlam]
                                            · linarith only [h19744, h31608, hlam]
                                          · linarith only [h31607, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      rcases p31592_3 (m.d 0 2) (by simp) with h31612 | h31612
                                      · linarith only [h31612, h4, hlam]
                                      · linarith only [h0, h31612, hlam]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h1, h23337, h31394, h31406, hc12, hc23, hlam, hphi, p31592_1]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h22010, hc02, hc23, hlam, hphi, p31592_1]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h0, h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31592_1]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h31408, hc12, hc45, hlam, hphi, ht23, ht34, p31592_1]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h31406, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h31408, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      rcases p31592_3 (m.d 0 2) (by simp) with h31623 | h31623
                                      · linarith only [h31623, hlam, p31592_0]
                                      · rcases p31592_3 (m.d 1 2) (by simp) with h31625 | h31625
                                        · linarith only [h31398, h31625, hlam]
                                        · rcases p31592_3 (m.d 2 3) (by simp) with h31627 | h31627
                                          · rcases p31592_3 (m.d 2 4) (by simp) with h31628 | h31628
                                            · linarith only [h31408, h31628, hlam]
                                            · linarith only [h19744, h31628, hlam]
                                          · linarith only [h31627, h4, hlam]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      rcases p31592_3 (m.d 0 2) (by simp) with h31632 | h31632
                                      · linarith only [h22010, h31632, hlam]
                                      · linarith only [h0, h31632, hlam]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h31407, hlam, p31592_0]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p31592_1]
                                    · have p31592_0 := h31592c.1
                                      have p31592_1 := h31592c.2.1
                                      have p31592_2 := h31592c.2.2.1
                                      have p31592_3 := h31592c.2.2.2
                                      linarith only [hlam, p31592_0]
                        · linarith only [h31443, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h0, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h31394, hlam, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h31396, hlam, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h31398, hlam, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h1, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h1, h23337, hc12, hc34, hlam, hphi, ht23, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h31400, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h31402, hlam, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h2, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h2, h30177, hc12, hc45, hlam, hphi, ht23, ht34, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h2, h30177, hc13, hc45, hlam, hphi, ht34, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h31404, hlam, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h3, hlam, p31414_0]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h29475, h3, h31407, hc12, hc23, hlam, hphi, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h29475, h3, h31394, h31407, hc12, hc23, hlam, hphi, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [h29475, h3, h31396, h31407, hc12, hc23, hlam, hphi, p31414_1]
                      · have p31414_0 := h31414c.1
                        have p31414_1 := h31414c.2.1
                        have p31414_2 := h31414c.2.2.1
                        have p31414_3 := h31414c.2.2.2
                        linarith only [hlam, p31414_0]
                · linarith only [h23337, h31406, h31407, hc03, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h31660 | h31660
                · linarith only [h1, h29475, h31394, h31406, h31660, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h31662 | h31662
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h31663 | h31663
                    · rcases h1bigk with h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c | h31664c
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        rcases p31664_3 (m.d 0 1) (by simp) with h31666 | h31666
                        · rcases p31664_3 (m.d 1 2) (by simp) with h31667 | h31667
                          · linarith only [h31667, hlam, p31664_0]
                          · rcases p31664_3 (m.d 1 3) (by simp) with h31669 | h31669
                            · linarith only [h1, h31669, hlam]
                            · linarith only [h31394, h31669, hlam]
                        · linarith only [h31666, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        rcases p31664_3 (m.d 0 1) (by simp) with h31673 | h31673
                        · rcases p31664_3 (m.d 1 2) (by simp) with h31674 | h31674
                          · linarith only [h0, h31674, hlam]
                          · rcases p31664_3 (m.d 1 3) (by simp) with h31676 | h31676
                            · linarith only [h31676, hlam, p31664_0]
                            · rcases p31664_3 (m.d 1 4) (by simp) with h31678 | h31678
                              · linarith only [h2, h31678, hlam]
                              · linarith only [h31400, h31678, hlam]
                        · linarith only [h31673, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        rcases p31664_3 (m.d 0 1) (by simp) with h31682 | h31682
                        · rcases p31664_3 (m.d 1 2) (by simp) with h31683 | h31683
                          · linarith only [h0, h31683, hlam]
                          · rcases p31664_3 (m.d 1 3) (by simp) with h31685 | h31685
                            · linarith only [h1, h31685, hlam]
                            · rcases p31664_3 (m.d 1 4) (by simp) with h31687 | h31687
                              · linarith only [h31687, hlam, p31664_0]
                              · rcases p31664_3 (m.d 1 5) (by simp) with h31689 | h31689
                                · linarith only [h3, h31689, hlam]
                                · linarith only [h31404, h31689, hlam]
                        · linarith only [h31682, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        rcases p31664_3 (m.d 0 1) (by simp) with h31693 | h31693
                        · rcases p31664_3 (m.d 1 2) (by simp) with h31694 | h31694
                          · linarith only [h0, h31694, hlam]
                          · rcases p31664_3 (m.d 1 3) (by simp) with h31696 | h31696
                            · linarith only [h1, h31696, hlam]
                            · rcases p31664_3 (m.d 1 4) (by simp) with h31698 | h31698
                              · linarith only [h2, h31698, hlam]
                              · rcases p31664_3 (m.d 1 5) (by simp) with h31700 | h31700
                                · linarith only [h31700, hlam, p31664_0]
                                · rcases h1emax with h31702 | h31702 | h31702 | h31702 | h31702
                                  · linarith only [h31702, hc15, hlam, hphi, ht01, ht0b, ht5b, p31664_1]
                                  · rcases h2bigk with h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c | h31704c
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31660, h31663, h4, hc12, hc34, hlam, hphi, ht23, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h4, hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h19744, hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h22010, hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h0, hlam, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31394, hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31396, hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31398, hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31660, h31663, hc02, hc34, hlam, hphi, ht23, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31660, h31663, hc12, hc34, hlam, hphi, ht23, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31406, hlam, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31660, hlam, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      rcases p31704_3 (m.d 0 2) (by simp) with h31720 | h31720
                                      · linarith only [h31720, hlam, p31704_0]
                                      · rcases p31704_3 (m.d 1 2) (by simp) with h31722 | h31722
                                        · linarith only [h31396, h31722, hlam]
                                        · rcases p31704_3 (m.d 2 3) (by simp) with h31724 | h31724
                                          · linarith only [h31406, h31724, hlam]
                                          · linarith only [h31724, h4, hlam]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      rcases p31704_3 (m.d 0 2) (by simp) with h31727 | h31727
                                      · linarith only [h19744, h31727, hlam]
                                      · linarith only [h0, h31727, hlam]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h0, h31406, h4, hc12, hc34, hlam, hphi, ht23, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [hlam, p31704_0]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h0, h22010, h31406, hc12, hc34, hlam, hphi, ht23, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      rcases p31704_3 (m.d 0 2) (by simp) with h31733 | h31733
                                      · linarith only [h31733, hlam, p31704_0]
                                      · rcases p31704_3 (m.d 1 2) (by simp) with h31735 | h31735
                                        · linarith only [h31398, h31735, hlam]
                                        · rcases p31704_3 (m.d 2 3) (by simp) with h31737 | h31737
                                          · linarith only [h31660, h31737, hlam]
                                          · linarith only [h31737, h4, hlam]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      rcases p31704_3 (m.d 0 2) (by simp) with h31740 | h31740
                                      · linarith only [h22010, h31740, hlam]
                                      · linarith only [h0, h31740, hlam]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [h31662, hlam, p31704_1]
                                    · have p31704_0 := h31704c.1
                                      have p31704_1 := h31704c.2.1
                                      have p31704_2 := h31704c.2.2.1
                                      have p31704_3 := h31704c.2.2.2
                                      linarith only [hlam, p31704_0]
                                  · rcases h2bigk with h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c | h31746c
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h4, hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h19744, hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h22010, hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h0, hlam, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31394, hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31396, hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31398, hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31406, hc02, hc34, hlam, hphi, ht23, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31406, hc12, hc34, hlam, hphi, ht23, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31406, hlam, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31660, hlam, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      rcases p31746_3 (m.d 0 2) (by simp) with h31762 | h31762
                                      · linarith only [h31762, hlam, p31746_0]
                                      · rcases p31746_3 (m.d 1 2) (by simp) with h31764 | h31764
                                        · linarith only [h31396, h31764, hlam]
                                        · rcases p31746_3 (m.d 2 3) (by simp) with h31766 | h31766
                                          · linarith only [h31406, h31766, hlam]
                                          · linarith only [h31766, h4, hlam]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      rcases p31746_3 (m.d 0 2) (by simp) with h31769 | h31769
                                      · linarith only [h19744, h31769, hlam]
                                      · linarith only [h0, h31769, hlam]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h0, h31406, h4, hc12, hc34, hlam, hphi, ht23, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [hlam, p31746_0]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h0, h22010, h31406, hc12, hc34, hlam, hphi, ht23, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      rcases p31746_3 (m.d 0 2) (by simp) with h31775 | h31775
                                      · linarith only [h31775, hlam, p31746_0]
                                      · rcases p31746_3 (m.d 1 2) (by simp) with h31777 | h31777
                                        · linarith only [h31398, h31777, hlam]
                                        · rcases p31746_3 (m.d 2 3) (by simp) with h31779 | h31779
                                          · linarith only [h31660, h31779, hlam]
                                          · linarith only [h31779, h4, hlam]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      rcases p31746_3 (m.d 0 2) (by simp) with h31782 | h31782
                                      · linarith only [h22010, h31782, hlam]
                                      · linarith only [h0, h31782, hlam]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [h31662, hlam, p31746_1]
                                    · have p31746_0 := h31746c.1
                                      have p31746_1 := h31746c.2.1
                                      have p31746_2 := h31746c.2.2.1
                                      have p31746_3 := h31746c.2.2.2
                                      linarith only [hlam, p31746_0]
                                  · rcases h2bigk with h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c | h31788c
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h4, hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h19744, hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h22010, hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h0, hlam, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31394, hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31396, hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31398, hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31406, hc02, hc34, hlam, hphi, ht23, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31406, hc12, hc34, hlam, hphi, ht23, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31406, hlam, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31660, hlam, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      rcases p31788_3 (m.d 0 2) (by simp) with h31804 | h31804
                                      · linarith only [h31804, hlam, p31788_0]
                                      · rcases p31788_3 (m.d 1 2) (by simp) with h31806 | h31806
                                        · linarith only [h31396, h31806, hlam]
                                        · rcases p31788_3 (m.d 2 3) (by simp) with h31808 | h31808
                                          · linarith only [h31406, h31808, hlam]
                                          · linarith only [h31808, h4, hlam]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      rcases p31788_3 (m.d 0 2) (by simp) with h31811 | h31811
                                      · linarith only [h19744, h31811, hlam]
                                      · linarith only [h0, h31811, hlam]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h0, h31406, h4, hc12, hc34, hlam, hphi, ht23, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [hlam, p31788_0]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h0, h22010, h31406, hc12, hc34, hlam, hphi, ht23, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      rcases p31788_3 (m.d 0 2) (by simp) with h31817 | h31817
                                      · linarith only [h31817, hlam, p31788_0]
                                      · rcases p31788_3 (m.d 1 2) (by simp) with h31819 | h31819
                                        · linarith only [h31398, h31819, hlam]
                                        · rcases p31788_3 (m.d 2 3) (by simp) with h31821 | h31821
                                          · linarith only [h31660, h31821, hlam]
                                          · linarith only [h31821, h4, hlam]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      rcases p31788_3 (m.d 0 2) (by simp) with h31824 | h31824
                                      · linarith only [h22010, h31824, hlam]
                                      · linarith only [h0, h31824, hlam]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [h31662, hlam, p31788_1]
                                    · have p31788_0 := h31788c.1
                                      have p31788_1 := h31788c.2.1
                                      have p31788_2 := h31788c.2.2.1
                                      have p31788_3 := h31788c.2.2.2
                                      linarith only [hlam, p31788_0]
                                  · rcases h2bigk with h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c | h31830c
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h4, hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h19744, hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h22010, hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h0, hlam, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31394, hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31396, hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31398, hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31406, hc02, hc34, hlam, hphi, ht23, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31406, hc12, hc34, hlam, hphi, ht23, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31406, hlam, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31660, hlam, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      rcases p31830_3 (m.d 0 2) (by simp) with h31846 | h31846
                                      · linarith only [h31846, hlam, p31830_0]
                                      · rcases p31830_3 (m.d 1 2) (by simp) with h31848 | h31848
                                        · linarith only [h31396, h31848, hlam]
                                        · rcases p31830_3 (m.d 2 3) (by simp) with h31850 | h31850
                                          · linarith only [h31406, h31850, hlam]
                                          · linarith only [h31850, h4, hlam]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      rcases p31830_3 (m.d 0 2) (by simp) with h31853 | h31853
                                      · linarith only [h19744, h31853, hlam]
                                      · linarith only [h0, h31853, hlam]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h0, h31406, h4, hc12, hc34, hlam, hphi, ht23, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [hlam, p31830_0]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h0, h22010, h31406, hc12, hc34, hlam, hphi, ht23, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      rcases p31830_3 (m.d 0 2) (by simp) with h31859 | h31859
                                      · linarith only [h31859, hlam, p31830_0]
                                      · rcases p31830_3 (m.d 1 2) (by simp) with h31861 | h31861
                                        · linarith only [h31398, h31861, hlam]
                                        · rcases p31830_3 (m.d 2 3) (by simp) with h31863 | h31863
                                          · linarith only [h31660, h31863, hlam]
                                          · linarith only [h31863, h4, hlam]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      rcases p31830_3 (m.d 0 2) (by simp) with h31866 | h31866
                                      · linarith only [h22010, h31866, hlam]
                                      · linarith only [h0, h31866, hlam]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [h31662, hlam, p31830_1]
                                    · have p31830_0 := h31830c.1
                                      have p31830_1 := h31830c.2.1
                                      have p31830_2 := h31830c.2.2.1
                                      have p31830_3 := h31830c.2.2.2
                                      linarith only [hlam, p31830_0]
                        · linarith only [h31693, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h0, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h31394, hlam, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h31396, hlam, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h31398, hlam, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h1, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h1, h23337, h30177, h31406, h31662, hc12, hc34, hlam, hphi, ht23, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h31400, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h31402, hlam, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h2, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h2, h30177, h31406, h31662, hc12, hc34, hlam, hphi, ht23, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h2, h30177, h31406, h31662, hc13, hc34, hlam, hphi, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h31404, hlam, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h3, hlam, p31664_0]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h3, h30177, h31406, h31662, hc12, hc34, hlam, hphi, ht23, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h3, h30177, h31394, h31406, h31662, hc12, hc34, hlam, hphi, ht23, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [h3, h30177, h31396, h31406, h31662, hc12, hc34, hlam, hphi, ht23, p31664_1]
                      · have p31664_0 := h31664c.1
                        have p31664_1 := h31664c.2.1
                        have p31664_2 := h31664c.2.2.1
                        have p31664_3 := h31664c.2.2.2
                        linarith only [hlam, p31664_0]
                    · linarith only [h31406, h31662, h31663, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h31894 | h31894
                    · linarith only [h0, h31406, h31662, h31894, h4, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h31406, h31894, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1 (m : N7Model)
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
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h29475 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h30177 | h30177
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475 h30177

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1 (m : N7Model)
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
    (h23337 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h29475 | h29475
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337 h29475

set_option maxHeartbeats 17120000 in
set_option maxHeartbeats 17120000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23 (m : N7Model)
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h23337 | h23337
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 h23337

end R2N4
