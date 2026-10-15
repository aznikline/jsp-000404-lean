import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S4
import Jsp000404.R1LeavesN7_1S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2564 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h3456 | h3456
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3457 | h3457
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3458 | h3458
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3459 | h3459
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3460 | h3460
          · linarith only [h2, h3460, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3462 | h3462
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3463 | h3463
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3464 | h3464
                · linarith only [h2, h3456, h3464, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3466 | h3466
                  · linarith only [h2, h3456, h3462, h3466, h9, hlam]
                  · rcases h0bigk with h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c | h3468c
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h2564, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3468_1]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h2564, h3456, h3462, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      rcases p3468_3 (m.d 0 1) (by simp) with h3472 | h3472
                      · rcases p3468_3 (m.d 0 2) (by simp) with h3473 | h3473
                        · linarith only [h0, h3473, hlam]
                        · linarith only [h3473, h5, hlam]
                      · linarith only [h2, h3472, hlam]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      rcases p3468_3 (m.d 0 1) (by simp) with h3477 | h3477
                      · rcases p3468_3 (m.d 0 2) (by simp) with h3478 | h3478
                        · linarith only [h0, h3478, hlam]
                        · linarith only [h3478, h6, hlam]
                      · linarith only [h3, h3477, hlam]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h0, hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h0, h2564, h3457, h3462, h3464, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3468_1]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      rcases p3468_3 (m.d 0 1) (by simp) with h3485 | h3485
                      · rcases p3468_3 (m.d 0 2) (by simp) with h3486 | h3486
                        · rcases p3468_3 (m.d 0 3) (by simp) with h3487 | h3487
                          · linarith only [h3487, h4, hlam]
                          · linarith only [h3487, h7, hlam]
                        · linarith only [h3486, h5, hlam]
                      · linarith only [h2, h3485, hlam]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      rcases p3468_3 (m.d 0 1) (by simp) with h3492 | h3492
                      · rcases p3468_3 (m.d 0 2) (by simp) with h3493 | h3493
                        · rcases p3468_3 (m.d 0 3) (by simp) with h3494 | h3494
                          · linarith only [h3494, h4, hlam]
                          · linarith only [h3494, h8, hlam]
                        · linarith only [h3493, h6, hlam]
                      · linarith only [h3, h3492, hlam]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h1, hlam, p3468_1]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h4, hlam, p3468_1]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      rcases p3468_3 (m.d 0 1) (by simp) with h3502 | h3502
                      · rcases p3468_3 (m.d 0 2) (by simp) with h3503 | h3503
                        · rcases p3468_3 (m.d 0 3) (by simp) with h3504 | h3504
                          · rcases p3468_3 (m.d 0 4) (by simp) with h3505 | h3505
                            · linarith only [h3505, h7, hlam]
                            · rcases p3468_3 (m.d 0 5) (by simp) with h3507 | h3507
                              · linarith only [h3507, h8, hlam]
                              · linarith only [h3507, h9, hlam]
                          · linarith only [h3504, h7, hlam]
                        · linarith only [h3503, h5, hlam]
                      · linarith only [h2, h3502, hlam]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      rcases p3468_3 (m.d 0 1) (by simp) with h3513 | h3513
                      · rcases p3468_3 (m.d 0 2) (by simp) with h3514 | h3514
                        · rcases p3468_3 (m.d 0 3) (by simp) with h3515 | h3515
                          · rcases p3468_3 (m.d 0 4) (by simp) with h3516 | h3516
                            · linarith only [h3516, h7, hlam]
                            · rcases p3468_3 (m.d 0 5) (by simp) with h3518 | h3518
                              · linarith only [h3518, h8, hlam]
                              · rcases h2bigk with h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c | h3520c
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  rcases p3520_3 (m.d 0 2) (by simp) with h3522 | h3522
                                  · rcases p3520_3 (m.d 1 2) (by simp) with h3523 | h3523
                                    · linarith only [h0, h3523, hlam]
                                    · rcases p3520_3 (m.d 2 3) (by simp) with h3525 | h3525
                                      · linarith only [h3525, h4, hlam]
                                      · linarith only [h2564, h3525, hlam]
                                  · linarith only [h0, h3522, hlam]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h0, h2564, h3457, h3462, h3464, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h2564, h3457, h3464, h4, hlam, p3520_2]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h2564, h3457, h4, hlam, p3520_2]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h0, hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h2564, hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h2564, h3462, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h0, h2564, h3462, h3464, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h4, hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h0, h3456, h3462, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  rcases p3520_3 (m.d 0 2) (by simp) with h3540 | h3540
                                  · rcases p3520_3 (m.d 1 2) (by simp) with h3541 | h3541
                                    · linarith only [h2564, h3541, hlam]
                                    · linarith only [h3456, h3541, hlam]
                                  · linarith only [h3540, h5, hlam]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  rcases p3520_3 (m.d 0 2) (by simp) with h3545 | h3545
                                  · rcases p3520_3 (m.d 1 2) (by simp) with h3546 | h3546
                                    · linarith only [h2564, h3546, hlam]
                                    · linarith only [h3457, h3546, hlam]
                                  · linarith only [h3545, h6, hlam]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h5, hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h3456, hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h3462, hlam, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h3464, hlam, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h6, hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h3457, hlam, p3520_0]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h3463, hlam, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [h0, h3457, h3462, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3520_1]
                                · have p3520_0 := h3520c.1
                                  have p3520_1 := h3520c.2.1
                                  have p3520_2 := h3520c.2.2.1
                                  have p3520_3 := h3520c.2.2.2
                                  linarith only [hlam, p3520_0]
                          · linarith only [h3515, h8, hlam]
                        · linarith only [h3514, h6, hlam]
                      · linarith only [h3, h3513, hlam]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h2, hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h5, hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h7, hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h9, hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h3, hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h6, hlam, p3468_1]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [h8, hlam, p3468_0]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      rcases p3468_3 (m.d 0 1) (by simp) with h3571 | h3571
                      · rcases p3468_3 (m.d 0 2) (by simp) with h3572 | h3572
                        · rcases p3468_3 (m.d 0 3) (by simp) with h3573 | h3573
                          · rcases p3468_3 (m.d 0 4) (by simp) with h3574 | h3574
                            · linarith only [h3574, h9, hlam]
                            · rcases p3468_3 (m.d 0 5) (by simp) with h3576 | h3576
                              · rcases h2bigk with h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c | h3577c
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  rcases p3577_3 (m.d 0 2) (by simp) with h3579 | h3579
                                  · rcases p3577_3 (m.d 1 2) (by simp) with h3580 | h3580
                                    · linarith only [h0, h3580, hlam]
                                    · rcases p3577_3 (m.d 2 3) (by simp) with h3582 | h3582
                                      · linarith only [h3582, h4, hlam]
                                      · linarith only [h2564, h3582, hlam]
                                  · linarith only [h0, h3579, hlam]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h0, h2564, h3456, h3462, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h2564, h3456, h4, hlam, p3577_2]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h2564, h3457, h4, hlam, p3577_2]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h0, hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h2564, hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h0, h2564, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h0, h2564, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h4, hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h0, h3456, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  rcases p3577_3 (m.d 0 2) (by simp) with h3597 | h3597
                                  · rcases p3577_3 (m.d 1 2) (by simp) with h3598 | h3598
                                    · linarith only [h2564, h3598, hlam]
                                    · linarith only [h3456, h3598, hlam]
                                  · linarith only [h3597, h5, hlam]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  rcases p3577_3 (m.d 0 2) (by simp) with h3602 | h3602
                                  · rcases p3577_3 (m.d 1 2) (by simp) with h3603 | h3603
                                    · linarith only [h2564, h3603, hlam]
                                    · linarith only [h3457, h3603, hlam]
                                  · linarith only [h3602, h6, hlam]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h5, hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h3456, hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h3462, hlam, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h3464, hlam, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h6, hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h3457, hlam, p3577_0]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h3463, hlam, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [h0, h3457, h3462, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3577_1]
                                · have p3577_0 := h3577c.1
                                  have p3577_1 := h3577c.2.1
                                  have p3577_2 := h3577c.2.2.1
                                  have p3577_3 := h3577c.2.2.2
                                  linarith only [hlam, p3577_0]
                              · linarith only [h3576, h9, hlam]
                          · linarith only [h3573, h7, hlam]
                        · linarith only [h3572, h5, hlam]
                      · linarith only [h2, h3571, hlam]
                    · have p3468_0 := h3468c.1
                      have p3468_1 := h3468c.2.1
                      have p3468_2 := h3468c.2.2.1
                      have p3468_3 := h3468c.2.2.2
                      linarith only [hlam, p3468_0]
              · linarith only [h0, h2564, h3456, h3462, h3463, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2564, h3457, h3462, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h2564, h3457, h3459, hlam]
      · linarith only [h2564, h3456, h3458, h7, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3626 | h3626
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3627 | h3627
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3628 | h3628
          · linarith only [h2, h3628, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3630 | h3630
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3631 | h3631
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3632 | h3632
                · linarith only [h2, h3456, h3632, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3634 | h3634
                  · linarith only [h3456, h3457, h3630, h3634, h6, h9, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c | h3636c
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h3457, h3631, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h3456, h3457, h3630, h3631, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      rcases p3636_3 (m.d 0 1) (by simp) with h3640 | h3640
                      · rcases p3636_3 (m.d 0 2) (by simp) with h3641 | h3641
                        · linarith only [h0, h3641, hlam]
                        · linarith only [h3641, h5, hlam]
                      · linarith only [h2, h3640, hlam]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h3456, h3457, h3630, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h0, hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h3456, h3457, h3630, h3631, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      rcases p3636_3 (m.d 0 1) (by simp) with h3649 | h3649
                      · rcases p3636_3 (m.d 0 2) (by simp) with h3650 | h3650
                        · rcases p3636_3 (m.d 0 3) (by simp) with h3651 | h3651
                          · linarith only [h3651, h4, hlam]
                          · linarith only [h3651, h7, hlam]
                        · linarith only [h3650, h5, hlam]
                      · linarith only [h2, h3649, hlam]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h0, h3456, h3457, h3630, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h1, hlam, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h4, hlam, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      rcases p3636_3 (m.d 0 1) (by simp) with h3660 | h3660
                      · rcases p3636_3 (m.d 0 2) (by simp) with h3661 | h3661
                        · rcases p3636_3 (m.d 0 3) (by simp) with h3662 | h3662
                          · rcases p3636_3 (m.d 0 4) (by simp) with h3663 | h3663
                            · linarith only [h3663, h7, hlam]
                            · rcases p3636_3 (m.d 0 5) (by simp) with h3665 | h3665
                              · linarith only [h3665, h8, hlam]
                              · linarith only [h3665, h9, hlam]
                          · linarith only [h3662, h7, hlam]
                        · linarith only [h3661, h5, hlam]
                      · linarith only [h2, h3660, hlam]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h3456, h3457, h3630, h6, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h2, hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h5, hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h7, hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h9, hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h3, hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h6, hlam, p3636_1]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [h8, hlam, p3636_0]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      rcases p3636_3 (m.d 0 1) (by simp) with h3680 | h3680
                      · rcases p3636_3 (m.d 0 2) (by simp) with h3681 | h3681
                        · rcases p3636_3 (m.d 0 3) (by simp) with h3682 | h3682
                          · rcases p3636_3 (m.d 0 4) (by simp) with h3683 | h3683
                            · linarith only [h3683, h9, hlam]
                            · rcases p3636_3 (m.d 0 5) (by simp) with h3685 | h3685
                              · rcases h2bigk with h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c | h3686c
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  rcases p3686_3 (m.d 0 2) (by simp) with h3688 | h3688
                                  · rcases p3686_3 (m.d 1 2) (by simp) with h3689 | h3689
                                    · linarith only [h0, h3689, hlam]
                                    · rcases p3686_3 (m.d 2 3) (by simp) with h3691 | h3691
                                      · linarith only [h3691, h4, hlam]
                                      · linarith only [h2564, h3691, hlam]
                                  · linarith only [h0, h3688, hlam]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h0, h3456, h3457, h3630, h3631, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h3456, h3457, h3631, h4, hlam, p3686_2]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h3456, h3457, h3630, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h0, hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h2564, hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h0, h3457, h3630, h3631, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h3457, hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h4, hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h0, h3456, h3630, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  rcases p3686_3 (m.d 0 2) (by simp) with h3706 | h3706
                                  · rcases p3686_3 (m.d 1 2) (by simp) with h3707 | h3707
                                    · linarith only [h2564, h3707, hlam]
                                    · linarith only [h3456, h3707, hlam]
                                  · linarith only [h3706, h5, hlam]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h0, h3456, h3457, h3630, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h5, hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h3456, hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h3630, hlam, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h3632, hlam, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h6, hlam, p3686_0]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h0, h3456, h3630, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [h3631, hlam, p3686_1]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  rcases p3686_3 (m.d 0 2) (by simp) with h3720 | h3720
                                  · rcases p3686_3 (m.d 1 2) (by simp) with h3721 | h3721
                                    · linarith only [h3457, h3721, hlam]
                                    · linarith only [h3456, h3721, hlam]
                                  · linarith only [h3720, h5, hlam]
                                · have p3686_0 := h3686c.1
                                  have p3686_1 := h3686c.2.1
                                  have p3686_2 := h3686c.2.2.1
                                  have p3686_3 := h3686c.2.2.2
                                  linarith only [hlam, p3686_0]
                              · linarith only [h3685, h9, hlam]
                          · linarith only [h3682, h7, hlam]
                        · linarith only [h3681, h5, hlam]
                      · linarith only [h2, h3680, hlam]
                    · have p3636_0 := h3636c.1
                      have p3636_1 := h3636c.2.1
                      have p3636_2 := h3636c.2.2.1
                      have p3636_3 := h3636c.2.2.2
                      linarith only [hlam, p3636_0]
              · linarith only [h2564, h3456, h3630, h3631, h8, h9, hc34, hc45, hlam, hphi]
            · linarith only [h0, h2564, h3456, h3630, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3733 | h3733
          · linarith only [h2, h3733, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3735 | h3735
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3736 | h3736
              · linarith only [h0, h2564, h3456, h3627, h3735, h3736, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h2564, h3456, h3735, h3736, h8, h9, hc34, hc45, hlam, hphi]
            · linarith only [h0, h2564, h3456, h3735, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h2564, h3456, h3626, h7, h9, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3741 | h3741
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3742 | h3742
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3743 | h3743
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3744 | h3744
          · linarith only [h3456, h3741, h3744, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3456, h3741, h3744, hlam]
        · linarith only [h3456, h3741, h3742, h3743, h5, h9, hc34, hc45, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3748 | h3748
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3749 | h3749
          · linarith only [h2564, h3741, h3742, h3749, h7, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3456, h3741, h3749, hlam]
        · linarith only [h2564, h3741, h3748, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3753 | h3753
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3754 | h3754
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3755 | h3755
          · linarith only [h3456, h3755, h5, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3757 | h3757
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3758 | h3758
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3759 | h3759
                · linarith only [h3759, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3761 | h3761
                  · linarith only [h3456, h3753, h3761, h5, h9, hlam]
                  · rcases h0bigk with h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c | h3763c
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h3456, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3766 | h3766
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3767 | h3767
                        · linarith only [h0, h3767, hlam]
                        · linarith only [h3767, h4, hlam]
                      · linarith only [h1, h3766, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3771 | h3771
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3772 | h3772
                        · linarith only [h0, h3772, hlam]
                        · linarith only [h3772, h5, hlam]
                      · linarith only [h2, h3771, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3776 | h3776
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3777 | h3777
                        · linarith only [h0, h3777, hlam]
                        · linarith only [h3777, h6, hlam]
                      · linarith only [h3, h3776, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h0, hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3783 | h3783
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3784 | h3784
                        · rcases p3763_3 (m.d 0 3) (by simp) with h3785 | h3785
                          · linarith only [h3785, h4, hlam]
                          · rcases p3763_3 (m.d 0 4) (by simp) with h3787 | h3787
                            · linarith only [h3787, h5, hlam]
                            · rcases p3763_3 (m.d 0 5) (by simp) with h3789 | h3789
                              · linarith only [h3789, h6, hlam]
                              · rcases h2bigk with h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h3456, h5, h8, h9, hlam, p3763_1, p3791_2]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  rcases p3791_3 (m.d 0 2) (by simp) with h3794 | h3794
                                  · rcases p3791_3 (m.d 1 2) (by simp) with h3795 | h3795
                                    · linarith only [h0, h3795, hlam]
                                    · rcases p3791_3 (m.d 2 3) (by simp) with h3797 | h3797
                                      · linarith only [h3797, hlam, p3791_0]
                                      · rcases p3791_3 (m.d 2 4) (by simp) with h3799 | h3799
                                        · linarith only [h3799, h5, hlam]
                                        · rcases p3791_3 (m.d 2 5) (by simp) with h3801 | h3801
                                          · linarith only [h3801, h6, hlam]
                                          · rcases h3bigk with h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, h3456, h3758, h3759, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, h3761, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h1, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h2564, hlam, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, h1, h3761, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h4, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3791_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h0, h3761, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h7, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h3753, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h3757, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h3761, hlam, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h8, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h3754, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h3758, hlam, p3803_0]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [h1, h3754, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3803_1]
                                            · have p3803_0 := h3803c.1
                                              have p3803_1 := h3803c.2.1
                                              have p3803_2 := h3803c.2.2.1
                                              have p3803_3 := h3803c.2.2.2
                                              linarith only [hlam, p3803_0]
                                  · linarith only [h3794, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  rcases p3791_3 (m.d 0 2) (by simp) with h3830 | h3830
                                  · rcases p3791_3 (m.d 1 2) (by simp) with h3831 | h3831
                                    · linarith only [h0, h3831, hlam]
                                    · rcases p3791_3 (m.d 2 3) (by simp) with h3833 | h3833
                                      · linarith only [h3833, h4, hlam]
                                      · linarith only [h3757, h3833, hlam]
                                  · linarith only [h3830, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  rcases p3791_3 (m.d 0 2) (by simp) with h3837 | h3837
                                  · rcases p3791_3 (m.d 1 2) (by simp) with h3838 | h3838
                                    · linarith only [h0, h3838, hlam]
                                    · rcases p3791_3 (m.d 2 3) (by simp) with h3840 | h3840
                                      · linarith only [h3840, h4, hlam]
                                      · linarith only [h3758, h3840, hlam]
                                  · linarith only [h3837, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h0, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h2564, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h3456, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h3741, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h4, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h0, h3456, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h0, h3456, h3759, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h5, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h3757, hlam, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h3759, hlam, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h6, hlam, p3791_0]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h3758, hlam, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3791_1]
                                · have p3791_0 := h3791c.1
                                  have p3791_1 := h3791c.2.1
                                  have p3791_2 := h3791c.2.2.1
                                  have p3791_3 := h3791c.2.2.2
                                  linarith only [hlam, p3791_0]
                        · linarith only [h3784, h4, hlam]
                      · linarith only [h1, h3783, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3866 | h3866
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3867 | h3867
                        · rcases p3763_3 (m.d 0 3) (by simp) with h3868 | h3868
                          · linarith only [h3868, h4, hlam]
                          · linarith only [h3868, h7, hlam]
                        · linarith only [h3867, h5, hlam]
                      · linarith only [h2, h3866, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3873 | h3873
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3874 | h3874
                        · rcases p3763_3 (m.d 0 3) (by simp) with h3875 | h3875
                          · linarith only [h3875, h4, hlam]
                          · linarith only [h3875, h8, hlam]
                        · linarith only [h3874, h6, hlam]
                      · linarith only [h3, h3873, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h1, hlam, p3763_1]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h4, hlam, p3763_1]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3883 | h3883
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3884 | h3884
                        · rcases p3763_3 (m.d 0 3) (by simp) with h3885 | h3885
                          · rcases p3763_3 (m.d 0 4) (by simp) with h3886 | h3886
                            · linarith only [h3886, h7, hlam]
                            · rcases p3763_3 (m.d 0 5) (by simp) with h3888 | h3888
                              · linarith only [h3888, h8, hlam]
                              · linarith only [h3888, h9, hlam]
                          · linarith only [h3885, h7, hlam]
                        · linarith only [h3884, h5, hlam]
                      · linarith only [h2, h3883, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      rcases p3763_3 (m.d 0 1) (by simp) with h3894 | h3894
                      · rcases p3763_3 (m.d 0 2) (by simp) with h3895 | h3895
                        · rcases p3763_3 (m.d 0 3) (by simp) with h3896 | h3896
                          · rcases p3763_3 (m.d 0 4) (by simp) with h3897 | h3897
                            · linarith only [h3897, h7, hlam]
                            · rcases p3763_3 (m.d 0 5) (by simp) with h3899 | h3899
                              · linarith only [h3899, h8, hlam]
                              · rcases h2bigk with h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c | h3901c
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h3456, h4, h5, h9, hlam, p3763_1, p3901_2]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  rcases p3901_3 (m.d 0 2) (by simp) with h3904 | h3904
                                  · rcases p3901_3 (m.d 1 2) (by simp) with h3905 | h3905
                                    · linarith only [h0, h3905, hlam]
                                    · rcases p3901_3 (m.d 2 3) (by simp) with h3907 | h3907
                                      · linarith only [h3907, hlam, p3901_0]
                                      · rcases p3901_3 (m.d 2 4) (by simp) with h3909 | h3909
                                        · linarith only [h3909, h5, hlam]
                                        · rcases p3901_3 (m.d 2 5) (by simp) with h3911 | h3911
                                          · linarith only [h3911, h6, hlam]
                                          · rcases h3bigk with h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c | h3913c
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              rcases p3913_3 (m.d 0 3) (by simp) with h3915 | h3915
                                              · rcases p3913_3 (m.d 1 3) (by simp) with h3916 | h3916
                                                · linarith only [h1, h3916, hlam]
                                                · rcases p3913_3 (m.d 2 3) (by simp) with h3918 | h3918
                                                  · linarith only [h3918, h4, hlam]
                                                  · linarith only [h2564, h3918, hlam]
                                              · linarith only [h1, h3915, hlam]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              rcases p3913_3 (m.d 0 3) (by simp) with h3922 | h3922
                                              · rcases p3913_3 (m.d 1 3) (by simp) with h3923 | h3923
                                                · linarith only [h1, h3923, hlam]
                                                · rcases p3913_3 (m.d 2 3) (by simp) with h3925 | h3925
                                                  · linarith only [h3925, h4, hlam]
                                                  · rcases p3913_3 (m.d 3 4) (by simp) with h3927 | h3927
                                                    · linarith only [h3927, h7, hlam]
                                                    · rcases p3913_3 (m.d 3 5) (by simp) with h3929 | h3929
                                                      · linarith only [h3929, h8, hlam]
                                                      · rcases h5bigk with h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3763_1, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h0, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p3763_1, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3763_1, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h9, hlam, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3, hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3741, hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3755, hlam, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h6, hlam, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h0, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p3763_1, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3759, hlam, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h8, hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3754, hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3758, hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [hlam, p3931_0]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3761, hlam, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h9, hc04, hc45, hlam, hphi, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3456, h3755, hc12, hc45, hlam, hphi, ht23, ht34, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3741, hc12, hc45, hlam, hphi, ht23, ht34, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [h3761, hc34, hc45, hlam, hphi, p3931_1]
                                                        · have p3931_0 := h3931c.1
                                                          have p3931_1 := h3931c.2.1
                                                          have p3931_2 := h3931c.2.2.1
                                                          have p3931_3 := h3931c.2.2.2
                                                          linarith only [hlam, p3931_0]
                                              · linarith only [h3922, h4, hlam]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              rcases p3913_3 (m.d 0 3) (by simp) with h3958 | h3958
                                              · rcases p3913_3 (m.d 1 3) (by simp) with h3959 | h3959
                                                · linarith only [h1, h3959, hlam]
                                                · linarith only [h3753, h3959, hlam]
                                              · linarith only [h3958, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              rcases p3913_3 (m.d 0 3) (by simp) with h3963 | h3963
                                              · rcases p3913_3 (m.d 1 3) (by simp) with h3964 | h3964
                                                · linarith only [h1, h3964, hlam]
                                                · linarith only [h3754, h3964, hlam]
                                              · linarith only [h3963, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h1, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h2564, hlam, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h0, h2564, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3901_1, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h0, h2564, h3761, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3901_1, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h4, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3901_1, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3901_1, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h0, h3761, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3901_1, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h7, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h3753, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h3757, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h3761, hlam, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h8, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h3754, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h3758, hlam, p3913_0]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [h1, h3754, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3913_1]
                                            · have p3913_0 := h3913c.1
                                              have p3913_1 := h3913c.2.1
                                              have p3913_2 := h3913c.2.2.1
                                              have p3913_3 := h3913c.2.2.2
                                              linarith only [hlam, p3913_0]
                                  · linarith only [h3904, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  rcases p3901_3 (m.d 0 2) (by simp) with h3989 | h3989
                                  · rcases p3901_3 (m.d 1 2) (by simp) with h3990 | h3990
                                    · linarith only [h0, h3990, hlam]
                                    · rcases p3901_3 (m.d 2 3) (by simp) with h3992 | h3992
                                      · linarith only [h3992, h4, hlam]
                                      · linarith only [h3757, h3992, hlam]
                                  · linarith only [h3989, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  rcases p3901_3 (m.d 0 2) (by simp) with h3996 | h3996
                                  · rcases p3901_3 (m.d 1 2) (by simp) with h3997 | h3997
                                    · linarith only [h0, h3997, hlam]
                                    · rcases p3901_3 (m.d 2 3) (by simp) with h3999 | h3999
                                      · linarith only [h3999, h4, hlam]
                                      · linarith only [h3758, h3999, hlam]
                                  · linarith only [h3996, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h0, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h2564, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h3456, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h3741, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h4, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  rcases p3901_3 (m.d 0 2) (by simp) with h4009 | h4009
                                  · rcases p3901_3 (m.d 1 2) (by simp) with h4010 | h4010
                                    · linarith only [h4010, hlam, p3901_0]
                                    · rcases p3901_3 (m.d 2 3) (by simp) with h4012 | h4012
                                      · rcases p3901_3 (m.d 2 4) (by simp) with h4013 | h4013
                                        · linarith only [h3757, h4013, hlam]
                                        · linarith only [h3456, h4013, hlam]
                                      · linarith only [h4012, hlam, p3901_0]
                                  · linarith only [h0, h4009, hlam]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h0, h3456, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h0, h3456, h3759, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h5, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h5, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h3757, hlam, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h3759, hlam, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h6, hlam, p3901_0]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3763_1, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h3758, hlam, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3763_1, p3901_1]
                                · have p3901_0 := h3901c.1
                                  have p3901_1 := h3901c.2.1
                                  have p3901_2 := h3901c.2.2.1
                                  have p3901_3 := h3901c.2.2.2
                                  linarith only [hlam, p3901_0]
                          · linarith only [h3896, h8, hlam]
                        · linarith only [h3895, h6, hlam]
                      · linarith only [h3, h3894, hlam]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h2, hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h5, hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h7, hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h9, hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h3, hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h6, hlam, p3763_1]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h8, hlam, p3763_0]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [h3456, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3763_1]
                    · have p3763_0 := h3763c.1
                      have p3763_1 := h3763c.2.1
                      have p3763_2 := h3763c.2.2.1
                      have p3763_3 := h3763c.2.2.2
                      linarith only [hlam, p3763_0]
              · linarith only [h2564, h3754, h3758, hlam]
            · linarith only [h2564, h3757, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4046 | h4046
          · linarith only [h2, h4046, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4048 | h4048
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4049 | h4049
              · linarith only [h0, h3753, h3754, h4, h4049, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4051 | h4051
                · linarith only [h4051, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4053 | h4053
                  · linarith only [h1, h3753, h4049, h4053, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c | h4055c
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h3456, h4, h4048, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h3456, h4048, h4049, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      rcases p4055_3 (m.d 0 1) (by simp) with h4059 | h4059
                      · rcases p4055_3 (m.d 0 2) (by simp) with h4060 | h4060
                        · linarith only [h0, h4060, hlam]
                        · linarith only [h4060, h5, hlam]
                      · linarith only [h2, h4059, hlam]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h3456, h4048, h4049, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h0, hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h3456, h4048, h4049, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      rcases p4055_3 (m.d 0 1) (by simp) with h4068 | h4068
                      · rcases p4055_3 (m.d 0 2) (by simp) with h4069 | h4069
                        · rcases p4055_3 (m.d 0 3) (by simp) with h4070 | h4070
                          · linarith only [h4, h4070, hlam]
                          · linarith only [h4070, h7, hlam]
                        · linarith only [h4069, h5, hlam]
                      · linarith only [h2, h4068, hlam]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h0, h3456, h4048, h4049, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h1, hlam, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h4, hlam, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      rcases p4055_3 (m.d 0 1) (by simp) with h4079 | h4079
                      · rcases p4055_3 (m.d 0 2) (by simp) with h4080 | h4080
                        · rcases p4055_3 (m.d 0 3) (by simp) with h4081 | h4081
                          · rcases p4055_3 (m.d 0 4) (by simp) with h4082 | h4082
                            · linarith only [h4082, h7, hlam]
                            · rcases p4055_3 (m.d 0 5) (by simp) with h4084 | h4084
                              · linarith only [h4084, h8, hlam]
                              · linarith only [h4084, h9, hlam]
                          · linarith only [h4081, h7, hlam]
                        · linarith only [h4080, h5, hlam]
                      · linarith only [h2, h4079, hlam]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h3456, h4048, h4049, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h2, hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h5, hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h7, hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h9, hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h3, hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h6, hlam, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h8, hlam, p4055_0]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [h3456, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p4055_1]
                    · have p4055_0 := h4055c.1
                      have p4055_1 := h4055c.2.1
                      have p4055_2 := h4055c.2.2.1
                      have p4055_3 := h4055c.2.2.2
                      linarith only [hlam, p4055_0]
            · linarith only [h2564, h3753, h4048, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4102 | h4102
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4103 | h4103
          · linarith only [h3753, h4102, h4103, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3753, h4102, h4103, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4106 | h4106
          · linarith only [h2, h3753, h4106, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4108 | h4108
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4109 | h4109
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4110 | h4110
                · linarith only [h4110, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4112 | h4112
                  · linarith only [h4108, h4112, h5, h9, hlam]
                  · rcases h0bigk with h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c | h4114c
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h4, h4102, h4106, h4109, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4114_1]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h2564, h3753, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4114_1]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      rcases p4114_3 (m.d 0 1) (by simp) with h4118 | h4118
                      · rcases p4114_3 (m.d 0 2) (by simp) with h4119 | h4119
                        · linarith only [h0, h4119, hlam]
                        · linarith only [h4119, h5, hlam]
                      · linarith only [h2, h4118, hlam]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      rcases p4114_3 (m.d 0 1) (by simp) with h4123 | h4123
                      · rcases p4114_3 (m.d 0 2) (by simp) with h4124 | h4124
                        · linarith only [h0, h4124, hlam]
                        · linarith only [h4124, h6, hlam]
                      · linarith only [h3, h4123, hlam]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h0, hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h2564, h3753, h4, h4109, h4112, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4114_1]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      rcases p4114_3 (m.d 0 1) (by simp) with h4131 | h4131
                      · rcases p4114_3 (m.d 0 2) (by simp) with h4132 | h4132
                        · rcases p4114_3 (m.d 0 3) (by simp) with h4133 | h4133
                          · linarith only [h4, h4133, hlam]
                          · linarith only [h4133, h7, hlam]
                        · linarith only [h4132, h5, hlam]
                      · linarith only [h2, h4131, hlam]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      rcases p4114_3 (m.d 0 1) (by simp) with h4138 | h4138
                      · rcases p4114_3 (m.d 0 2) (by simp) with h4139 | h4139
                        · rcases p4114_3 (m.d 0 3) (by simp) with h4140 | h4140
                          · linarith only [h4, h4140, hlam]
                          · linarith only [h4140, h8, hlam]
                        · linarith only [h4139, h6, hlam]
                      · linarith only [h3, h4138, hlam]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h1, hlam, p4114_1]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h4, hlam, p4114_1]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      rcases p4114_3 (m.d 0 1) (by simp) with h4148 | h4148
                      · rcases p4114_3 (m.d 0 2) (by simp) with h4149 | h4149
                        · rcases p4114_3 (m.d 0 3) (by simp) with h4150 | h4150
                          · rcases p4114_3 (m.d 0 4) (by simp) with h4151 | h4151
                            · linarith only [h4151, h7, hlam]
                            · rcases p4114_3 (m.d 0 5) (by simp) with h4153 | h4153
                              · linarith only [h4153, h8, hlam]
                              · linarith only [h4153, h9, hlam]
                          · linarith only [h4150, h7, hlam]
                        · linarith only [h4149, h5, hlam]
                      · linarith only [h2, h4148, hlam]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      rcases p4114_3 (m.d 0 1) (by simp) with h4159 | h4159
                      · rcases p4114_3 (m.d 0 2) (by simp) with h4160 | h4160
                        · rcases p4114_3 (m.d 0 3) (by simp) with h4161 | h4161
                          · rcases p4114_3 (m.d 0 4) (by simp) with h4162 | h4162
                            · linarith only [h4162, h7, hlam]
                            · rcases p4114_3 (m.d 0 5) (by simp) with h4164 | h4164
                              · linarith only [h4164, h8, hlam]
                              · rcases h2bigk with h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h2564, h3753, h4, h4109, h4112, hlam, p4166_2]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h2564, h3753, h4109, h4112, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  rcases p4166_3 (m.d 0 2) (by simp) with h4170 | h4170
                                  · rcases p4166_3 (m.d 1 2) (by simp) with h4171 | h4171
                                    · linarith only [h0, h4171, hlam]
                                    · rcases p4166_3 (m.d 2 3) (by simp) with h4173 | h4173
                                      · linarith only [h4, h4173, hlam]
                                      · linarith only [h4108, h4173, hlam]
                                  · linarith only [h4170, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  rcases p4166_3 (m.d 0 2) (by simp) with h4177 | h4177
                                  · rcases p4166_3 (m.d 1 2) (by simp) with h4178 | h4178
                                    · linarith only [h0, h4178, hlam]
                                    · rcases p4166_3 (m.d 2 3) (by simp) with h4180 | h4180
                                      · linarith only [h4, h4180, hlam]
                                      · linarith only [h4109, h4180, hlam]
                                  · linarith only [h4177, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h2564, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3456, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h3741, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  rcases p4166_3 (m.d 0 2) (by simp) with h4190 | h4190
                                  · rcases p4166_3 (m.d 1 2) (by simp) with h4191 | h4191
                                    · linarith only [h4191, hlam, p4166_0]
                                    · rcases p4166_3 (m.d 2 3) (by simp) with h4193 | h4193
                                      · rcases p4166_3 (m.d 2 4) (by simp) with h4194 | h4194
                                        · linarith only [h4108, h4194, hlam]
                                        · linarith only [h3456, h4194, hlam]
                                      · linarith only [h4193, hlam, p4166_0]
                                  · linarith only [h0, h4190, hlam]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h2564, h3753, h4108, hc12, hc23, hlam, hphi, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, h2564, h3753, h4, h4108, h4110, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h5, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4108, hlam, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4110, hlam, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h6, hlam, p4166_0]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4114_1, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h4109, hlam, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4114_1, p4166_1]
                                · have p4166_0 := h4166c.1
                                  have p4166_1 := h4166c.2.1
                                  have p4166_2 := h4166c.2.2.1
                                  have p4166_3 := h4166c.2.2.2
                                  linarith only [hlam, p4166_0]
                          · linarith only [h4161, h8, hlam]
                        · linarith only [h4160, h6, hlam]
                      · linarith only [h3, h4159, hlam]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h2, hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h5, hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h7, hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h9, hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h3, hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h6, hlam, p4114_1]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h8, hlam, p4114_0]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [h2564, h3753, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34, p4114_1]
                    · have p4114_0 := h4114c.1
                      have p4114_1 := h4114c.2.1
                      have p4114_2 := h4114c.2.2.1
                      have p4114_3 := h4114c.2.2.2
                      linarith only [hlam, p4114_0]
              · linarith only [h0, h2564, h3753, h4, h4108, h4109, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h2564, h4108, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h2564 | h2564
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2564
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2564

set_option maxHeartbeats 8436000 in
set_option maxHeartbeats 8436000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9

end R2N4
