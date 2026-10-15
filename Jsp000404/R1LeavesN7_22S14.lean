import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h437 | h437
  · rcases m.htr 1 2 5 (by decide) (by decide) with h438 | h438
    · linarith only [h0, h10, h4, h438, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h440 | h440
      · rcases m.htr 1 3 5 (by decide) (by decide) with h441 | h441
        · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
          · linarith only [h0, h10, h4, h437, h442, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
            · rcases m.htr 2 3 5 (by decide) (by decide) with h445 | h445
              · rcases m.htr 2 4 5 (by decide) (by decide) with h446 | h446
                · linarith only [h0, h4, h437, h438, h442, h445, h446, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                  · linarith only [h437, h438, h444, h446, h448, hlam]
                  · rcases h2bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      rcases p450_3 (m.d 0 2) (by simp) with h452 | h452
                      · rcases p450_3 (m.d 1 2) (by simp) with h453 | h453
                        · linarith only [h0, h453, hlam]
                        · rcases p450_3 (m.d 2 3) (by simp) with h455 | h455
                          · linarith only [h4, h455, hlam]
                          · linarith only [h10, h455, hlam]
                      · linarith only [h0, h452, hlam]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h0, h10, h437, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h437, h438, h6, hlam, p450_2]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h0, h437, h438, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h0, hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h10, hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h438, h446, hc24, hc45, hlam, hphi, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h438, hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h4, hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h0, h4, h437, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      rcases p450_3 (m.d 0 2) (by simp) with h470 | h470
                      · rcases p450_3 (m.d 1 2) (by simp) with h471 | h471
                        · linarith only [h10, h471, hlam]
                        · linarith only [h437, h471, hlam]
                      · linarith only [h470, h5, hlam]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p450_1, u5ehi2]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h5, hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h437, hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h444, hlam, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h446, hlam, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h6, hlam, p450_0]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h0, h437, h444, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [h445, hlam, p450_1]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      rcases p450_3 (m.d 0 2) (by simp) with h484 | h484
                      · rcases p450_3 (m.d 1 2) (by simp) with h485 | h485
                        · linarith only [h438, h485, hlam]
                        · linarith only [h437, h485, hlam]
                      · linarith only [h484, h5, hlam]
                    · have p450_0 := h450c.1
                      have p450_1 := h450c.2.1
                      have p450_2 := h450c.2.2.1
                      have p450_3 := h450c.2.2.2
                      linarith only [hlam, p450_0]
              · linarith only [h10, h437, h441, h444, h445, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h437, h444, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h492 | h492
          · linarith only [h0, h10, h4, h437, h492, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
            · rcases m.htr 2 3 5 (by decide) (by decide) with h495 | h495
              · linarith only [h0, h10, h4, h437, h441, h495, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h437, h494, h495, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h437, h494, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h437, h440, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
    · linarith only [h0, h10, h4, h500, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h502 | h502
      · rcases m.htr 1 3 5 (by decide) (by decide) with h503 | h503
        · rcases m.htr 1 4 5 (by decide) (by decide) with h504 | h504
          · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
            · rcases m.htr 2 3 5 (by decide) (by decide) with h506 | h506
              · rcases m.htr 2 4 5 (by decide) (by decide) with h507 | h507
                · rcases m.htr 3 4 5 (by decide) (by decide) with h508 | h508
                  · linarith only [h1, h502, h508, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases h2bigk with h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      rcases p510_3 (m.d 0 2) (by simp) with h512 | h512
                      · rcases p510_3 (m.d 1 2) (by simp) with h513 | h513
                        · linarith only [h0, h513, hlam]
                        · rcases p510_3 (m.d 2 3) (by simp) with h515 | h515
                          · linarith only [h4, h515, hlam]
                          · linarith only [h10, h515, hlam]
                      · linarith only [h0, h512, hlam]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h0, h437, h504, h505, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p510_1]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h0, h437, h504, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p510_1]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      rcases p510_3 (m.d 0 2) (by simp) with h521 | h521
                      · rcases p510_3 (m.d 1 2) (by simp) with h522 | h522
                        · linarith only [h0, h522, hlam]
                        · rcases p510_3 (m.d 2 3) (by simp) with h524 | h524
                          · linarith only [h4, h524, hlam]
                          · linarith only [h506, h524, hlam]
                      · linarith only [h521, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h0, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h10, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h437, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h500, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h4, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      rcases p510_3 (m.d 0 2) (by simp) with h534 | h534
                      · rcases p510_3 (m.d 1 2) (by simp) with h535 | h535
                        · linarith only [h535, hlam, p510_0]
                        · rcases p510_3 (m.d 2 3) (by simp) with h537 | h537
                          · rcases p510_3 (m.d 2 4) (by simp) with h538 | h538
                            · linarith only [h505, h538, hlam]
                            · linarith only [h437, h538, hlam]
                          · linarith only [h537, hlam, p510_0]
                      · linarith only [h0, h534, hlam]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h437, h504, h508, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p510_1]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p510_1, u5ehi2]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h5, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      rcases p510_3 (m.d 0 2) (by simp) with h547 | h547
                      · rcases p510_3 (m.d 1 2) (by simp) with h548 | h548
                        · linarith only [h548, hlam, p510_0]
                        · rcases p510_3 (m.d 2 3) (by simp) with h550 | h550
                          · rcases p510_3 (m.d 2 4) (by simp) with h551 | h551
                            · rcases p510_3 (m.d 2 5) (by simp) with h552 | h552
                              · linarith only [h507, h552, hlam]
                              · linarith only [h500, h552, hlam]
                            · linarith only [h551, hlam, p510_0]
                          · linarith only [h10, h550, hlam]
                      · linarith only [h0, h547, hlam]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h505, hlam, p510_1]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h0, h4, h500, h505, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p510_1]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h6, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      rcases p510_3 (m.d 0 2) (by simp) with h562 | h562
                      · rcases p510_3 (m.d 1 2) (by simp) with h563 | h563
                        · linarith only [h563, hlam, p510_0]
                        · rcases p510_3 (m.d 2 3) (by simp) with h565 | h565
                          · rcases p510_3 (m.d 2 4) (by simp) with h566 | h566
                            · rcases p510_3 (m.d 2 5) (by simp) with h567 | h567
                              · rcases h3bigk with h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c | h568c
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, h4, h502, h504, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, h4, h437, h504, h505, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 3) (by simp) with h572 | h572
                                  · rcases p568_3 (m.d 1 3) (by simp) with h573 | h573
                                    · linarith only [h1, h573, hlam]
                                    · linarith only [h502, h573, hlam]
                                  · linarith only [h572, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 3) (by simp) with h577 | h577
                                  · rcases p568_3 (m.d 1 3) (by simp) with h578 | h578
                                    · linarith only [h1, h578, hlam]
                                    · linarith only [h503, h578, hlam]
                                  · linarith only [h577, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h1, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h10, hlam, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 3) (by simp) with h585 | h585
                                  · rcases p568_3 (m.d 1 3) (by simp) with h586 | h586
                                    · rcases p568_3 (m.d 2 3) (by simp) with h587 | h587
                                      · rcases p568_3 (m.d 3 4) (by simp) with h588 | h588
                                        · linarith only [h588, hlam, p568_0]
                                        · rcases p568_3 (m.d 3 5) (by simp) with h590 | h590
                                          · linarith only [h503, h590, hlam]
                                          · linarith only [h508, h590, hlam]
                                      · linarith only [h505, h587, hlam]
                                    · linarith only [h586, hlam, p568_0]
                                  · linarith only [h585, h7, hlam]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht5b, p568_1, u5ehi3]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h4, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, h4, h502, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  rcases p568_3 (m.d 0 3) (by simp) with h600 | h600
                                  · rcases p568_3 (m.d 1 3) (by simp) with h601 | h601
                                    · linarith only [h10, h601, hlam]
                                    · linarith only [h502, h601, hlam]
                                  · linarith only [h600, h7, hlam]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p568_1, u5ehi3]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h7, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h502, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h505, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h508, hlam, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h8, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h503, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h506, hlam, p568_0]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [h1, h503, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p568_1]
                                · have p568_0 := h568c.1
                                  have p568_1 := h568c.2.1
                                  have p568_2 := h568c.2.2.1
                                  have p568_3 := h568c.2.2.2
                                  linarith only [hlam, p568_0]
                              · linarith only [h567, hlam, p510_0]
                            · linarith only [h437, h566, hlam]
                          · linarith only [h10, h565, hlam]
                      · linarith only [h0, h562, hlam]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h506, hlam, p510_1]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [h507, hlam, p510_0]
                    · have p510_0 := h510c.1
                      have p510_1 := h510c.2.1
                      have p510_2 := h510c.2.2.1
                      have p510_3 := h510c.2.2.2
                      linarith only [hlam, p510_0]
                · linarith only [h437, h504, h507, hlam]
              · linarith only [h3, h437, h503, h504, h505, h506, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h10, h503, h505, h7, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h626 | h626
            · rcases m.htr 2 3 5 (by decide) (by decide) with h627 | h627
              · rcases m.htr 2 4 5 (by decide) (by decide) with h628 | h628
                · rcases m.htr 3 4 5 (by decide) (by decide) with h629 | h629
                  · linarith only [h502, h504, h629, hlam]
                  · rcases h2bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h4, h437, h504, h626, h628, hlam, p631_2]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, h437, h504, h626, h628, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, h437, h504, h628, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      rcases p631_3 (m.d 0 2) (by simp) with h636 | h636
                      · rcases p631_3 (m.d 1 2) (by simp) with h637 | h637
                        · linarith only [h0, h637, hlam]
                        · rcases p631_3 (m.d 2 3) (by simp) with h639 | h639
                          · linarith only [h4, h639, hlam]
                          · linarith only [h627, h639, hlam]
                      · linarith only [h636, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h10, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h437, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h500, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h4, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      rcases p631_3 (m.d 0 2) (by simp) with h649 | h649
                      · rcases p631_3 (m.d 1 2) (by simp) with h650 | h650
                        · linarith only [h650, hlam, p631_0]
                        · rcases p631_3 (m.d 2 3) (by simp) with h652 | h652
                          · rcases p631_3 (m.d 2 4) (by simp) with h653 | h653
                            · linarith only [h626, h653, hlam]
                            · linarith only [h437, h653, hlam]
                          · linarith only [h652, hlam, p631_0]
                      · linarith only [h0, h649, hlam]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h437, h504, h628, hc12, hc23, hlam, hphi, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p631_1, u5ehi2]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h5, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      rcases p631_3 (m.d 0 2) (by simp) with h662 | h662
                      · rcases p631_3 (m.d 1 2) (by simp) with h663 | h663
                        · linarith only [h663, hlam, p631_0]
                        · rcases p631_3 (m.d 2 3) (by simp) with h665 | h665
                          · rcases p631_3 (m.d 2 4) (by simp) with h666 | h666
                            · rcases p631_3 (m.d 2 5) (by simp) with h667 | h667
                              · linarith only [h628, h667, hlam]
                              · linarith only [h500, h667, hlam]
                            · linarith only [h666, hlam, p631_0]
                          · linarith only [h10, h665, hlam]
                      · linarith only [h0, h662, hlam]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h626, hlam, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h437, h504, h628, hc12, hc24, hlam, hphi, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h6, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      rcases p631_3 (m.d 0 2) (by simp) with h677 | h677
                      · rcases p631_3 (m.d 1 2) (by simp) with h678 | h678
                        · linarith only [h678, hlam, p631_0]
                        · rcases p631_3 (m.d 2 3) (by simp) with h680 | h680
                          · rcases p631_3 (m.d 2 4) (by simp) with h681 | h681
                            · rcases p631_3 (m.d 2 5) (by simp) with h682 | h682
                              · rcases h3bigk with h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h0, h4, h503, hc01, hlam, hphi, ht0b, ht5b, p683_1, u5ehi3]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h0, h10, h4, h503, hc01, hlam, hphi, ht0b, ht5b, p683_1, u5ehi3]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  rcases p683_3 (m.d 0 3) (by simp) with h687 | h687
                                  · rcases p683_3 (m.d 1 3) (by simp) with h688 | h688
                                    · linarith only [h1, h688, hlam]
                                    · linarith only [h502, h688, hlam]
                                  · linarith only [h687, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  rcases p683_3 (m.d 0 3) (by simp) with h692 | h692
                                  · rcases p683_3 (m.d 1 3) (by simp) with h693 | h693
                                    · linarith only [h1, h693, hlam]
                                    · linarith only [h503, h693, hlam]
                                  · linarith only [h692, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h1, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h10, hlam, p683_1]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  rcases p683_3 (m.d 0 3) (by simp) with h700 | h700
                                  · rcases p683_3 (m.d 1 3) (by simp) with h701 | h701
                                    · rcases p683_3 (m.d 2 3) (by simp) with h702 | h702
                                      · rcases p683_3 (m.d 3 4) (by simp) with h703 | h703
                                        · linarith only [h703, hlam, p683_0]
                                        · rcases p683_3 (m.d 3 5) (by simp) with h705 | h705
                                          · linarith only [h503, h705, hlam]
                                          · linarith only [h629, h705, hlam]
                                      · linarith only [h626, h702, hlam]
                                    · linarith only [h701, hlam, p683_0]
                                  · linarith only [h7, h700, hlam]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p683_1, u5ehi3]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h4, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h0, h4, h502, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p683_1]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  rcases p683_3 (m.d 0 3) (by simp) with h715 | h715
                                  · rcases p683_3 (m.d 1 3) (by simp) with h716 | h716
                                    · linarith only [h10, h716, hlam]
                                    · linarith only [h502, h716, hlam]
                                  · linarith only [h7, h715, hlam]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p683_1, u5ehi3]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h7, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h502, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h626, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h629, hlam, p683_1]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h8, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h503, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h627, hlam, p683_0]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [h1, h503, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p683_1]
                                · have p683_0 := h683c.1
                                  have p683_1 := h683c.2.1
                                  have p683_2 := h683c.2.2.1
                                  have p683_3 := h683c.2.2.2
                                  linarith only [hlam, p683_0]
                              · linarith only [h682, hlam, p631_0]
                            · linarith only [h437, h681, hlam]
                          · linarith only [h10, h680, hlam]
                      · linarith only [h0, h677, hlam]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h627, hlam, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h628, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h738 | h738
                  · linarith only [h437, h628, h738, hc12, hc34, hlam, hphi, ht23]
                  · rcases h2bigk with h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h4, h437, h628, h7, h9, hlam, p740_2]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h10, h503, hc02, hlam, hphi, ht0b, ht5b, p740_1, u5ehi3]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      rcases p740_3 (m.d 0 2) (by simp) with h744 | h744
                      · rcases p740_3 (m.d 1 2) (by simp) with h745 | h745
                        · linarith only [h0, h745, hlam]
                        · rcases p740_3 (m.d 2 3) (by simp) with h747 | h747
                          · linarith only [h4, h747, hlam]
                          · linarith only [h626, h747, hlam]
                      · linarith only [h744, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      rcases p740_3 (m.d 0 2) (by simp) with h751 | h751
                      · rcases p740_3 (m.d 1 2) (by simp) with h752 | h752
                        · linarith only [h0, h752, hlam]
                        · rcases p740_3 (m.d 2 3) (by simp) with h754 | h754
                          · linarith only [h4, h754, hlam]
                          · linarith only [h627, h754, hlam]
                      · linarith only [h751, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h0, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h10, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h437, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h500, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h4, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      rcases p740_3 (m.d 0 2) (by simp) with h764 | h764
                      · rcases p740_3 (m.d 1 2) (by simp) with h765 | h765
                        · linarith only [h765, hlam, p740_0]
                        · rcases p740_3 (m.d 2 3) (by simp) with h767 | h767
                          · rcases p740_3 (m.d 2 4) (by simp) with h768 | h768
                            · linarith only [h626, h768, hlam]
                            · linarith only [h437, h768, hlam]
                          · linarith only [h767, hlam, p740_0]
                      · linarith only [h0, h764, hlam]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h437, hc12, hc23, hlam, hphi, p740_1]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h0, h4, h500, hc01, hlam, hphi, ht0b, ht5b, p740_1, u5ehi1]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h5, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h0, h4, h628, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h626, hlam, p740_1]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h628, hlam, p740_1]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h6, hlam, p740_0]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      rcases p740_3 (m.d 0 2) (by simp) with h782 | h782
                      · rcases p740_3 (m.d 1 2) (by simp) with h783 | h783
                        · linarith only [h783, hlam, p740_0]
                        · rcases p740_3 (m.d 2 3) (by simp) with h785 | h785
                          · rcases p740_3 (m.d 2 4) (by simp) with h786 | h786
                            · linarith only [h628, h786, hlam]
                            · linarith only [h437, h786, hlam]
                          · linarith only [h10, h785, hlam]
                      · linarith only [h0, h782, hlam]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h627, hlam, p740_1]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [h0, h437, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p740_1]
                    · have p740_0 := h740c.1
                      have p740_1 := h740c.2.1
                      have p740_2 := h740c.2.2.1
                      have p740_3 := h740c.2.2.2
                      linarith only [hlam, p740_0]
              · linarith only [h1, h10, h503, h627, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h0, h10, h4, h502, h503, h504, h626, h7, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
          · linarith only [h0, h4, h502, h503, h796, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
            · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
              · linarith only [h0, h4, h502, h503, h799, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                · linarith only [h0, h4, h796, h798, h799, h8, h801, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h803 | h803
                  · linarith only [h1, h502, h801, h803, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases h2bigk with h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h4, h437, h7, h798, h799, h803, h9, hlam, p805_2]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      rcases p805_3 (m.d 0 2) (by simp) with h808 | h808
                      · rcases p805_3 (m.d 1 2) (by simp) with h809 | h809
                        · linarith only [h0, h809, hlam]
                        · rcases p805_3 (m.d 2 3) (by simp) with h811 | h811
                          · linarith only [h811, hlam, p805_0]
                          · rcases p805_3 (m.d 2 4) (by simp) with h813 | h813
                            · linarith only [h5, h813, hlam]
                            · rcases p805_3 (m.d 2 5) (by simp) with h815 | h815
                              · linarith only [h6, h815, hlam]
                              · linarith only [h799, h815, hlam]
                      · linarith only [h808, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      rcases p805_3 (m.d 0 2) (by simp) with h819 | h819
                      · rcases p805_3 (m.d 1 2) (by simp) with h820 | h820
                        · linarith only [h0, h820, hlam]
                        · rcases p805_3 (m.d 2 3) (by simp) with h822 | h822
                          · linarith only [h4, h822, hlam]
                          · linarith only [h798, h822, hlam]
                      · linarith only [h819, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      rcases p805_3 (m.d 0 2) (by simp) with h826 | h826
                      · rcases p805_3 (m.d 1 2) (by simp) with h827 | h827
                        · linarith only [h0, h827, hlam]
                        · rcases p805_3 (m.d 2 3) (by simp) with h829 | h829
                          · linarith only [h4, h829, hlam]
                          · rcases p805_3 (m.d 2 4) (by simp) with h831 | h831
                            · linarith only [h5, h831, hlam]
                            · rcases p805_3 (m.d 2 5) (by simp) with h833 | h833
                              · linarith only [h833, hlam, p805_0]
                              · rcases h3bigk with h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  rcases p835_3 (m.d 0 3) (by simp) with h837 | h837
                                  · rcases p835_3 (m.d 1 3) (by simp) with h838 | h838
                                    · linarith only [h1, h838, hlam]
                                    · rcases p835_3 (m.d 2 3) (by simp) with h840 | h840
                                      · linarith only [h4, h840, hlam]
                                      · linarith only [h10, h840, hlam]
                                  · linarith only [h1, h837, hlam]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  rcases p835_3 (m.d 0 3) (by simp) with h844 | h844
                                  · rcases p835_3 (m.d 1 3) (by simp) with h845 | h845
                                    · linarith only [h1, h845, hlam]
                                    · rcases p835_3 (m.d 2 3) (by simp) with h847 | h847
                                      · linarith only [h4, h847, hlam]
                                      · rcases p835_3 (m.d 3 4) (by simp) with h849 | h849
                                        · linarith only [h7, h849, hlam]
                                        · rcases p835_3 (m.d 3 5) (by simp) with h851 | h851
                                          · linarith only [h8, h851, hlam]
                                          · linarith only [h799, h851, hlam]
                                  · linarith only [h4, h844, hlam]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h10, h502, h7, h799, h803, h9, hlam, p835_2]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h0, h4, h437, h798, h799, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h1, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h10, hlam, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h0, h10, h4, h799, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h503, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h4, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h799, hc13, hc35, hlam, hphi, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h0, h4, h799, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h799, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h7, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h502, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h798, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h803, hlam, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h8, hlam, p835_0]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h0, h4, h502, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [h0, h10, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p835_1]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  rcases p835_3 (m.d 0 3) (by simp) with h875 | h875
                                  · rcases p835_3 (m.d 1 3) (by simp) with h876 | h876
                                    · linarith only [h503, h876, hlam]
                                    · linarith only [h502, h876, hlam]
                                  · linarith only [h7, h875, hlam]
                                · have p835_0 := h835c.1
                                  have p835_1 := h835c.2.1
                                  have p835_2 := h835c.2.2.1
                                  have p835_3 := h835c.2.2.2
                                  linarith only [hlam, p835_0]
                      · linarith only [h826, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h0, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h10, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h437, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h500, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h4, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h0, h4, h7, h799, h803, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p805_1]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h437, hc12, hc23, hlam, hphi, p805_1]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h799, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h5, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h0, h4, h7, h798, h799, h803, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p805_1]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h798, hlam, p805_1]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h801, hlam, p805_1]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h6, hlam, p805_0]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      rcases p805_3 (m.d 0 2) (by simp) with h898 | h898
                      · rcases p805_3 (m.d 1 2) (by simp) with h899 | h899
                        · linarith only [h899, hlam, p805_0]
                        · rcases p805_3 (m.d 2 3) (by simp) with h901 | h901
                          · linarith only [h799, h901, hlam]
                          · linarith only [h10, h901, hlam]
                      · linarith only [h0, h898, hlam]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h10, hc12, hc25, hlam, hphi, p805_1]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [h0, h4, h437, h7, h799, h803, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p805_1]
                    · have p805_0 := h805c.1
                      have p805_1 := h805c.2.1
                      have p805_2 := h805c.2.2.1
                      have p805_3 := h805c.2.2.2
                      linarith only [hlam, p805_0]
            · linarith only [h1, h10, h502, h798, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h909 | h909
        · linarith only [h0, h4, h502, h7, h909, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
          · rcases m.htr 2 3 4 (by decide) (by decide) with h912 | h912
            · linarith only [h0, h4, h502, h911, h912, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h914 | h914
              · linarith only [h909, h912, h914, hc13, hc34, hlam, hphi]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                  · rcases h2bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h10, h4, h7, h914, h917, hlam, p918_2]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      rcases p918_3 (m.d 0 2) (by simp) with h921 | h921
                      · rcases p918_3 (m.d 1 2) (by simp) with h922 | h922
                        · linarith only [h0, h922, hlam]
                        · rcases p918_3 (m.d 2 3) (by simp) with h924 | h924
                          · linarith only [h924, hlam, p918_0]
                          · rcases p918_3 (m.d 2 4) (by simp) with h926 | h926
                            · linarith only [h5, h926, hlam]
                            · linarith only [h912, h926, hlam]
                      · linarith only [h921, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h0, h437, h911, hc01, hlam, hphi, ht0b, ht5b, p918_1, u5ehi4]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      rcases p918_3 (m.d 0 2) (by simp) with h931 | h931
                      · rcases p918_3 (m.d 1 2) (by simp) with h932 | h932
                        · linarith only [h0, h932, hlam]
                        · rcases p918_3 (m.d 2 3) (by simp) with h934 | h934
                          · linarith only [h4, h934, hlam]
                          · rcases p918_3 (m.d 2 4) (by simp) with h936 | h936
                            · linarith only [h5, h936, hlam]
                            · linarith only [h916, h936, hlam]
                      · linarith only [h931, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h0, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h10, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h437, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h500, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h4, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h0, h4, h7, h914, h917, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p918_1]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h912, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h914, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h5, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      rcases p918_3 (m.d 0 2) (by simp) with h951 | h951
                      · rcases p918_3 (m.d 1 2) (by simp) with h952 | h952
                        · linarith only [h952, hlam, p918_0]
                        · rcases p918_3 (m.d 2 3) (by simp) with h954 | h954
                          · linarith only [h912, h954, hlam]
                          · linarith only [h10, h954, hlam]
                      · linarith only [h0, h951, hlam]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h10, hc12, hc24, hlam, hphi, p918_1]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h0, h4, h500, h7, h912, hc01, hlam, hphi, ht0b, ht5b, p918_1, u5ehi1]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h6, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      rcases p918_3 (m.d 0 2) (by simp) with h962 | h962
                      · rcases p918_3 (m.d 1 2) (by simp) with h963 | h963
                        · linarith only [h963, hlam, p918_0]
                        · rcases p918_3 (m.d 2 3) (by simp) with h965 | h965
                          · linarith only [h914, h965, hlam]
                          · linarith only [h10, h965, hlam]
                      · linarith only [h0, h962, hlam]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h10, hc12, hc25, hlam, hphi, p918_1]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [h916, hlam, p918_0]
                    · have p918_0 := h918c.1
                      have p918_1 := h918c.2.1
                      have p918_2 := h918c.2.2.1
                      have p918_3 := h918c.2.2.2
                      linarith only [hlam, p918_0]
                  · linarith only [h2, h437, h911, h912, h917, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h437, h911, h916, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h974 | h974
            · rcases m.htr 2 3 5 (by decide) (by decide) with h975 | h975
              · rcases m.htr 2 4 5 (by decide) (by decide) with h976 | h976
                · rcases m.htr 3 4 5 (by decide) (by decide) with h977 | h977
                  · linarith only [h0, h4, h911, h974, h977, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h10, h4, h502, h974, h976, h977, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h980 | h980
                  · linarith only [h974, h976, h980, hlam]
                  · rcases h2bigk with h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h10, h4, h502, h7, h9, h974, h976, hlam, p982_2]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h0, h909, h975, hc01, hlam, hphi, ht0b, ht5b, p982_1, u5ehi1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      rcases p982_3 (m.d 0 2) (by simp) with h986 | h986
                      · rcases p982_3 (m.d 1 2) (by simp) with h987 | h987
                        · linarith only [h0, h987, hlam]
                        · rcases p982_3 (m.d 2 3) (by simp) with h989 | h989
                          · linarith only [h4, h989, hlam]
                          · linarith only [h974, h989, hlam]
                      · linarith only [h986, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      rcases p982_3 (m.d 0 2) (by simp) with h993 | h993
                      · rcases p982_3 (m.d 1 2) (by simp) with h994 | h994
                        · linarith only [h0, h994, hlam]
                        · rcases p982_3 (m.d 2 3) (by simp) with h996 | h996
                          · linarith only [h4, h996, hlam]
                          · linarith only [h975, h996, hlam]
                      · linarith only [h993, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h0, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h10, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h437, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h500, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h4, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      rcases p982_3 (m.d 0 2) (by simp) with h1006 | h1006
                      · rcases p982_3 (m.d 1 2) (by simp) with h1007 | h1007
                        · linarith only [h1007, hlam, p982_0]
                        · rcases p982_3 (m.d 2 3) (by simp) with h1009 | h1009
                          · rcases p982_3 (m.d 2 4) (by simp) with h1010 | h1010
                            · linarith only [h1010, h974, hlam]
                            · linarith only [h1010, h437, hlam]
                          · linarith only [h1009, hlam, p982_0]
                      · linarith only [h0, h1006, hlam]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h10, h502, h974, hc12, hc23, hlam, hphi, p982_1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h0, h10, h4, h502, h974, h976, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p982_1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h5, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h0, h4, h7, h9, h976, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p982_1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h974, hlam, p982_1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h976, hlam, p982_1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h6, hlam, p982_0]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      rcases p982_3 (m.d 0 2) (by simp) with h1024 | h1024
                      · rcases p982_3 (m.d 1 2) (by simp) with h1025 | h1025
                        · linarith only [h1025, hlam, p982_0]
                        · rcases p982_3 (m.d 2 3) (by simp) with h1027 | h1027
                          · rcases p982_3 (m.d 2 4) (by simp) with h1028 | h1028
                            · linarith only [h1028, h976, hlam]
                            · linarith only [h1028, h437, hlam]
                          · linarith only [h10, h1027, hlam]
                      · linarith only [h0, h1024, hlam]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h975, hlam, p982_1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [h437, hc12, hc25, hlam, hphi, p982_1]
                    · have p982_0 := h982c.1
                      have p982_1 := h982c.2.1
                      have p982_2 := h982c.2.2.1
                      have p982_3 := h982c.2.2.2
                      linarith only [hlam, p982_0]
              · linarith only [h10, h502, h974, h975, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1037 | h1037
              · linarith only [h1037, h7, h974, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1039 | h1039
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1040 | h1040
                  · rcases h2bigk with h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h10, h1039, h5, h502, h911, hlam, p1041_2]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      rcases p1041_3 (m.d 0 2) (by simp) with h1044 | h1044
                      · rcases p1041_3 (m.d 1 2) (by simp) with h1045 | h1045
                        · linarith only [h0, h1045, hlam]
                        · rcases p1041_3 (m.d 2 3) (by simp) with h1047 | h1047
                          · linarith only [h1047, hlam, p1041_0]
                          · rcases p1041_3 (m.d 2 4) (by simp) with h1049 | h1049
                            · linarith only [h1049, h5, hlam]
                            · linarith only [h1049, h974, hlam]
                      · linarith only [h1044, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h0, h10, h1039, h502, h911, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1041_1]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      rcases p1041_3 (m.d 0 2) (by simp) with h1054 | h1054
                      · rcases p1041_3 (m.d 1 2) (by simp) with h1055 | h1055
                        · linarith only [h0, h1055, hlam]
                        · rcases p1041_3 (m.d 2 3) (by simp) with h1057 | h1057
                          · linarith only [h1057, h4, hlam]
                          · rcases p1041_3 (m.d 2 4) (by simp) with h1059 | h1059
                            · linarith only [h1059, h5, hlam]
                            · linarith only [h1039, h1059, hlam]
                      · linarith only [h1054, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h0, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h10, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h437, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h500, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h4, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h1037, h1040, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1041_1]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h974, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h1037, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h5, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      rcases p1041_3 (m.d 0 2) (by simp) with h1074 | h1074
                      · rcases p1041_3 (m.d 1 2) (by simp) with h1075 | h1075
                        · linarith only [h1075, hlam, p1041_0]
                        · rcases p1041_3 (m.d 2 3) (by simp) with h1077 | h1077
                          · linarith only [h1077, h974, hlam]
                          · linarith only [h10, h1077, hlam]
                      · linarith only [h0, h1074, hlam]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1041_1]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h0, h4, h7, h974, hc01, hlam, hphi, ht0b, ht5b, p1041_1, u5ehi2]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h6, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      rcases p1041_3 (m.d 0 2) (by simp) with h1085 | h1085
                      · rcases p1041_3 (m.d 1 2) (by simp) with h1086 | h1086
                        · linarith only [h1086, hlam, p1041_0]
                        · rcases p1041_3 (m.d 2 3) (by simp) with h1088 | h1088
                          · linarith only [h1037, h1088, hlam]
                          · linarith only [h10, h1088, hlam]
                      · linarith only [h0, h1085, hlam]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h10, hc12, hc25, hlam, hphi, p1041_1]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [h1039, hlam, p1041_0]
                    · have p1041_0 := h1041c.1
                      have p1041_1 := h1041c.2.1
                      have p1041_2 := h1041c.2.2.1
                      have p1041_3 := h1041c.2.2.2
                      linarith only [hlam, p1041_0]
                  · linarith only [h0, h10, h1040, h4, h7, h9, h974, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1096 | h1096
                  · linarith only [h1039, h1096, h437, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h10, h1096, h4, h7, h9, h974, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9 h10
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9 h10

end R2N4
