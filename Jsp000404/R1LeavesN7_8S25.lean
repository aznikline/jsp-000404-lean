import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S11
import Jsp000404.R1LeavesN7_8S23
import Jsp000404.R1LeavesN7_8S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16170000 in
set_option maxHeartbeats 16170000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7600 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h7601 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h8467 | h8467
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8468 | h8468
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8469 | h8469
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8470 | h8470
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8471 | h8471
          · linarith only [h7600, h7601, h8471, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8473 | h8473
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8474 | h8474
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8475 | h8475
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8476 | h8476
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8477 | h8477
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8478 | h8478
                      · linarith only [h7600, h8471, h8473, h8478, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8480 | h8480
                        · linarith only [h7600, h7601, h8478, h8480, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h7600, h7601, h8473, h8475, h8478, h8480, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h7600, h8473, h8477, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h8469, h8476, hlam]
                · linarith only [h0, h7600, h8473, h8475, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h7600, h7601, h8473, h8474, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8487 | h8487
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8488 | h8488
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8489 | h8489
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8490 | h8490
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8491 | h8491
                      · linarith only [h7600, h7601, h8471, h8489, h8491, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8493 | h8493
                        · linarith only [h7600, h7601, h8473, h8487, h8491, h8493, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8495 | h8495
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8496 | h8496
                            · linarith only [h7601, h8467, h8491, h8496, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8498 | h8498
                              · linarith only [h7600, h7601, h8488, h8491, h8498, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8500 | h8500
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8501 | h8501
                                  · rcases h0bigk with h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c | h8502c
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [hlam, p8502_0]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h0, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h7601, h8491, hc03, hc34, hlam, hphi, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h7601, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h7601, h8491, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8502_1, u5ehi0]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h0, h8467, hc12, hlam, hphi, ht01, ht0b, ht5b, p8502_1, u5ehi1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [hlam, p8502_0]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      rcases p8502_3 (m.d 0 1) (by simp) with h8510 | h8510
                                      · linarith only [h0, h8510, hlam]
                                      · linarith only [h7600, h8510, hlam]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h0, h7601, h8467, h8490, h8500, hc12, hlam, hphi, ht01, ht0b, ht5b, p8502_1, u5ehi4]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      rcases p8502_3 (m.d 0 1) (by simp) with h8514 | h8514
                                      · linarith only [h0, h8514, hlam]
                                      · linarith only [h8467, h8514, hlam]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h7600, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8468, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [hlam, p8502_0]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8471, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8473, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8467, h8490, h8500, hc04, hlam, hphi, ht0b, ht5b, p8502_1, u5ehi4]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8469, hlam, p8502_0]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      rcases p8502_3 (m.d 0 1) (by simp) with h8524 | h8524
                                      · linarith only [h7601, h8524, hlam]
                                      · linarith only [h7600, h8524, hlam]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [hlam, p8502_0]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      rcases p8502_3 (m.d 0 1) (by simp) with h8528 | h8528
                                      · linarith only [h7601, h8528, hlam]
                                      · linarith only [h8467, h8528, hlam]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8467, hlam, p8502_0]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8470, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h7600, h7601, h8467, h8488, h8491, hc23, hc34, hlam, hphi, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [h8487, hlam, p8502_1]
                                    · have p8502_0 := h8502c.1
                                      have p8502_1 := h8502c.2.1
                                      have p8502_2 := h8502c.2.2.1
                                      have p8502_3 := h8502c.2.2.2
                                      linarith only [hlam, p8502_0]
                                  · linarith only [h7601, h8491, h8500, h8501, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h7601, h8467, h8491, h8495, h8496, h8500, hc23, hc34, hlam, hphi]
                          · linarith only [h7601, h8467, h8495, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                    · linarith only [h0, h8467, h8490, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h8467, h8489, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h8467, h8488, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h7601, h8467, h8487, hlam]
        · linarith only [h0, h8467, h8470, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8544 | h8544
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8545 | h8545
          · linarith only [h0, h7600, h8469, h8545, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8547 | h8547
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8548 | h8548
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8549 | h8549
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8550 | h8550
                  · linarith only [h0, h7600, h8469, h8547, h8550, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h7600, h8547, h8550, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h7600, h8547, h8549, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h7600, h7601, h8547, h8548, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8555 | h8555
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8556 | h8556
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8557 | h8557
                  · linarith only [h8469, h8544, h8557, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h8467, h8557, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h8467, h8556, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h8467, h8469, h8555, hlam]
        · linarith only [h0, h8467, h8544, hlam]
    · linarith only [h0, h7600, h8468, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8564 | h8564
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8565 | h8565
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8566 | h8566
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8567 | h8567
          · linarith only [h7600, h7601, h8567, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8569 | h8569
            · linarith only [h7600, h8467, h8569, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8571 | h8571
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8572 | h8572
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8573 | h8573
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8574 | h8574
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8575 | h8575
                      · linarith only [h7600, h7601, h8567, h8573, h8575, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8577 | h8577
                        · linarith only [h7600, h8467, h8569, h8577, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8579 | h8579
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8580 | h8580
                            · linarith only [h7600, h8467, h8564, h8575, h8579, h8580, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8582 | h8582
                              · linarith only [h7600, h8467, h8572, h8577, h8582, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8584 | h8584
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8585 | h8585
                                  · rcases h0bigk with h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c | h8586c
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [hlam, p8586_0]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h0, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h7600, h8467, h8572, h8575, h8579, hc23, hc34, hlam, hphi, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h7601, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h8467, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      rcases p8586_3 (m.d 0 1) (by simp) with h8592 | h8592
                                      · linarith only [h0, h8592, hlam]
                                      · rcases p8586_3 (m.d 0 2) (by simp) with h8594 | h8594
                                        · rcases p8586_3 (m.d 0 3) (by simp) with h8595 | h8595
                                          · linarith only [h8564, h8595, hlam]
                                          · rcases p8586_3 (m.d 0 4) (by simp) with h8597 | h8597
                                            · linarith only [h8565, h8597, hlam]
                                            · linarith only [h7601, h8597, hlam]
                                        · linarith only [h0, h8594, hlam]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [hlam, p8586_0]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      rcases p8586_3 (m.d 0 1) (by simp) with h8602 | h8602
                                      · linarith only [h0, h8602, hlam]
                                      · linarith only [h7600, h8602, hlam]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h0, h8565, h8584, hc12, hlam, hphi, ht01, ht0b, ht5b, p8586_1, u5ehi4]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      rcases p8586_3 (m.d 0 1) (by simp) with h8606 | h8606
                                      · linarith only [h0, h8606, hlam]
                                      · rcases p8586_3 (m.d 0 2) (by simp) with h8608 | h8608
                                        · rcases p8586_3 (m.d 0 3) (by simp) with h8609 | h8609
                                          · linarith only [h8564, h8609, hlam]
                                          · rcases p8586_3 (m.d 0 4) (by simp) with h8611 | h8611
                                            · linarith only [h8565, h8611, hlam]
                                            · linarith only [h8571, h8611, hlam]
                                        · linarith only [h8566, h8608, hlam]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h7600, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h8564, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [hlam, p8586_0]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h8567, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h8569, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h7600, h7601, h8572, h8575, hc23, hc34, hlam, hphi, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h8565, hlam, p8586_0]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      rcases p8586_3 (m.d 0 1) (by simp) with h8622 | h8622
                                      · linarith only [h7601, h8622, hlam]
                                      · linarith only [h7600, h8622, hlam]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [hlam, p8586_0]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h7600, h7601, h8467, h8572, h8575, hc23, hc34, hlam, hphi, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h7600, h8467, h8572, h8575, h8579, hc23, hc34, hlam, hphi, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h8566, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      rcases p8586_3 (m.d 0 1) (by simp) with h8629 | h8629
                                      · linarith only [h8467, h8629, hlam]
                                      · linarith only [h7600, h8629, hlam]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [h8571, hlam, p8586_1]
                                    · have p8586_0 := h8586c.1
                                      have p8586_1 := h8586c.2.1
                                      have p8586_2 := h8586c.2.2.1
                                      have p8586_3 := h8586c.2.2.2
                                      linarith only [hlam, p8586_0]
                                  · linarith only [h7600, h7601, h8572, h8575, h8584, h8585, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8635 | h8635
                                  · rcases h0bigk with h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [hlam, p8636_0]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h0, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h7600, h8467, h8572, h8577, hc23, hc35, hlam, hphi, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h7601, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h8467, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      rcases p8636_3 (m.d 0 1) (by simp) with h8642 | h8642
                                      · linarith only [h0, h8642, hlam]
                                      · rcases p8636_3 (m.d 0 2) (by simp) with h8644 | h8644
                                        · rcases p8636_3 (m.d 0 3) (by simp) with h8645 | h8645
                                          · linarith only [h8564, h8645, hlam]
                                          · rcases p8636_3 (m.d 0 4) (by simp) with h8647 | h8647
                                            · linarith only [h8565, h8647, hlam]
                                            · linarith only [h7601, h8647, hlam]
                                        · linarith only [h0, h8644, hlam]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [hlam, p8636_0]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      rcases p8636_3 (m.d 0 1) (by simp) with h8652 | h8652
                                      · linarith only [h0, h8652, hlam]
                                      · linarith only [h7600, h8652, hlam]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h0, h8571, h8584, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      rcases p8636_3 (m.d 0 1) (by simp) with h8656 | h8656
                                      · linarith only [h0, h8656, hlam]
                                      · rcases p8636_3 (m.d 0 2) (by simp) with h8658 | h8658
                                        · rcases p8636_3 (m.d 0 3) (by simp) with h8659 | h8659
                                          · linarith only [h8564, h8659, hlam]
                                          · rcases p8636_3 (m.d 0 4) (by simp) with h8661 | h8661
                                            · linarith only [h8565, h8661, hlam]
                                            · linarith only [h8571, h8661, hlam]
                                        · linarith only [h8566, h8658, hlam]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h7600, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h8564, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [hlam, p8636_0]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h8567, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h8569, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h7600, h7601, h8572, h8575, hc23, hc34, hlam, hphi, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h8565, hlam, p8636_0]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      rcases p8636_3 (m.d 0 1) (by simp) with h8672 | h8672
                                      · linarith only [h7601, h8672, hlam]
                                      · linarith only [h7600, h8672, hlam]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [hlam, p8636_0]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h7600, h7601, h8467, h8572, h8575, hc23, hc34, hlam, hphi, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h7600, h8467, h8572, h8575, h8579, hc23, hc34, hlam, hphi, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h8566, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      rcases p8636_3 (m.d 0 1) (by simp) with h8679 | h8679
                                      · linarith only [h8467, h8679, hlam]
                                      · linarith only [h7600, h8679, hlam]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [h8571, hlam, p8636_1]
                                    · have p8636_0 := h8636c.1
                                      have p8636_1 := h8636c.2.1
                                      have p8636_2 := h8636c.2.2.1
                                      have p8636_3 := h8636c.2.2.2
                                      linarith only [hlam, p8636_0]
                                  · linarith only [h7600, h7601, h8572, h8575, h8635, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h7601, h8571, h8579, hlam]
                    · linarith only [h0, h8566, h8574, hlam]
                  · linarith only [h0, h8565, h8573, hlam]
                · linarith only [h0, h8564, h8572, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8689 | h8689
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8690 | h8690
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8691 | h8691
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8692 | h8692
                      · linarith only [h7600, h7601, h8571, h8692, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8694 | h8694
                        · linarith only [h7600, h7601, h8571, h8694, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8696 | h8696
                          · linarith only [h7600, h7601, h8571, h8692, h8696, hc13, hc34, hlam, hphi]
                          · linarith only [h7600, h7601, h8689, h8696, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h8566, h8691, hlam]
                  · linarith only [h0, h8565, h8690, hlam]
                · linarith only [h0, h8564, h8689, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8702 | h8702
          · linarith only [h7600, h7601, h8702, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8704 | h8704
            · linarith only [h0, h7600, h8566, h8704, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8706 | h8706
              · linarith only [h8565, h8566, h8706, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8708 | h8708
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8709 | h8709
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8710 | h8710
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8711 | h8711
                      · linarith only [h7600, h7601, h8565, h8566, h8702, h8710, h8711, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8713 | h8713
                        · linarith only [h7600, h7601, h8565, h8566, h8704, h8713, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8715 | h8715
                          · linarith only [h7600, h7601, h8706, h8711, h8715, hc13, hc34, hlam, hphi]
                          · linarith only [h7600, h7601, h8708, h8715, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8718 | h8718
                      · linarith only [h0, h7600, h8710, h8718, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8720 | h8720
                        · linarith only [h7600, h7601, h8709, h8710, h8720, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8722 | h8722
                          · linarith only [h7601, h8706, h8709, h8710, h8722, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h7600, h7601, h8708, h8722, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h7600, h8565, h8708, h8709, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h8564, h8708, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8727 | h8727
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8728 | h8728
          · linarith only [h0, h7600, h8565, h8728, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8730 | h8730
            · linarith only [h7600, h8467, h8730, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8732 | h8732
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8733 | h8733
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8734 | h8734
                  · linarith only [h8565, h8727, h8734, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8736 | h8736
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8737 | h8737
                      · linarith only [h7600, h8467, h8728, h8734, h8736, h8737, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8739 | h8739
                        · linarith only [h7600, h8467, h8730, h8734, h8736, h8739, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8741 | h8741
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8742 | h8742
                            · linarith only [h7600, h8467, h8564, h8565, h8734, h8736, h8737, h8742, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h7600, h8467, h8733, h8734, h8736, h8742, hc23, hc34, hlam, hphi]
                          · linarith only [h7600, h8467, h8733, h8734, h8736, h8741, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h8727, h8736, hlam]
                · linarith only [h0, h8564, h8733, hlam]
              · linarith only [h8565, h8727, h8732, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8749 | h8749
          · linarith only [h0, h7600, h8565, h8749, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8751 | h8751
            · linarith only [h7600, h8467, h8751, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8753 | h8753
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8754 | h8754
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8755 | h8755
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8756 | h8756
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8757 | h8757
                      · linarith only [h0, h7600, h8565, h8755, h8757, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8759 | h8759
                        · linarith only [h0, h7600, h8565, h8751, h8755, h8759, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8761 | h8761
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8762 | h8762
                            · linarith only [h0, h7600, h8565, h8754, h8755, h8757, h8762, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8764 | h8764
                              · linarith only [h0, h7600, h8565, h8754, h8755, h8764, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8766 | h8766
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8767 | h8767
                                  · rcases h0bigk with h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c | h8768c
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [hlam, p8768_0]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h0, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h0, h8727, h8755, h8766, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h7601, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8467, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8727, h8755, h8766, hc01, hc12, hlam, hphi, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [hlam, p8768_0]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h7600, h8727, h8754, h8755, h8766, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8565, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8727, hlam, p8768_0]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h7600, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8564, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [hlam, p8768_0]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8749, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8751, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h7600, h8565, h8754, h8755, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h0, h7600, h8565, h8754, h8755, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      rcases p8768_3 (m.d 0 1) (by simp) with h8786 | h8786
                                      · linarith only [h7601, h8786, hlam]
                                      · linarith only [h7600, h8786, hlam]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [hlam, p8768_0]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h0, h7600, h8565, h8727, h8754, h8755, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h7600, h8467, h8754, h8757, h8761, hc23, hc34, hlam, hphi, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h0, h7600, h8727, h8754, h8755, h8766, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      rcases p8768_3 (m.d 0 1) (by simp) with h8793 | h8793
                                      · linarith only [h8467, h8793, hlam]
                                      · linarith only [h7600, h8793, hlam]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [h8753, hlam, p8768_1]
                                    · have p8768_0 := h8768c.1
                                      have p8768_1 := h8768c.2.1
                                      have p8768_2 := h8768c.2.2.1
                                      have p8768_3 := h8768c.2.2.2
                                      linarith only [hlam, p8768_0]
                                  · linarith only [h8565, h8753, h8755, h8757, h8761, h8767, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                · linarith only [h8565, h8753, h8766, hlam]
                          · linarith only [h7600, h7601, h8753, h8754, h8761, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h7600, h8565, h8754, h8755, h8756, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8802 | h8802
                    · linarith only [h0, h7600, h8727, h8754, h8755, h8802, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8804 | h8804
                      · linarith only [h0, h7600, h8749, h8753, h8804, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8806 | h8806
                        · linarith only [h0, h7600, h8755, h8806, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8808 | h8808
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8809 | h8809
                            · linarith only [h0, h7600, h7601, h8754, h8755, h8804, h8809, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h7600, h8754, h8755, h8809, hc23, hc34, hlam, hphi]
                          · linarith only [h7600, h7601, h8754, h8808, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h7600, h8564, h8727, h8753, h8754, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8814 | h8814
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8815 | h8815
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8816 | h8816
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8817 | h8817
                      · linarith only [h0, h7600, h8565, h8815, h8817, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8819 | h8819
                        · linarith only [h0, h7600, h8565, h8815, h8819, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8821 | h8821
                          · linarith only [h7600, h7601, h8753, h8817, h8821, hc13, hc34, hlam, hphi]
                          · linarith only [h7600, h7601, h8814, h8821, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h7600, h8565, h8814, h8815, h8816, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8825 | h8825
                    · linarith only [h0, h7600, h8727, h8814, h8815, h8825, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8827 | h8827
                      · linarith only [h0, h7600, h8815, h8827, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8829 | h8829
                        · linarith only [h0, h7600, h8815, h8829, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8831 | h8831
                          · linarith only [h0, h7600, h8565, h8753, h8814, h8827, h8831, hc23, hc34, hlam, hphi]
                          · linarith only [h7600, h7601, h8814, h8831, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h7600, h8564, h8565, h8814, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h7600, h8564, hlam]

set_option maxHeartbeats 16170000 in
set_option maxHeartbeats 16170000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7600 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h7601 | h7601
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x0_x0 m hb0 hb2 hb3 hb5 hg0 h7600 h7601
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x0_x1 m hb0 hb2 hb3 hb5 hg0 h7600 h7601

set_option maxHeartbeats 16170000 in
set_option maxHeartbeats 16170000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s11 m hb0 hb2 hb3 hb5 h0 h7600

set_option maxHeartbeats 16170000 in
set_option maxHeartbeats 16170000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h7600 | h7600
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x0 m hb0 hb2 hb3 hb5 hg0 h7600
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10_x1 m hb0 hb2 hb3 hb5 hg0 h7600

set_option maxHeartbeats 31370000 in
set_option maxHeartbeats 31370000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s10 m hb0 hb2 hb3 hb5 h0

end R2N4
