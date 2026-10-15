import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S10
import Jsp000404.R1LeavesN7_3S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h6193 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h7464 | h7464
  · rcases m.htr 1 2 4 (by decide) (by decide) with h7465 | h7465
    · rcases m.htr 1 2 5 (by decide) (by decide) with h7466 | h7466
      · rcases m.htr 1 3 4 (by decide) (by decide) with h7467 | h7467
        · linarith only [h1, h7, h7467, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h7469 | h7469
          · linarith only [h1, h5823, h7469, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7471 | h7471
            · linarith only [h2, h6193, h7471, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7473 | h7473
              · linarith only [h1, h7, h7464, h7473, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7475 | h7475
                · linarith only [h4, h5823, h7475, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7477 | h7477
                  · linarith only [h0, h6193, h7, h7465, h7477, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7479 | h7479
                    · rcases h1bigk with h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c | h7480c
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        rcases p7480_3 (m.d 0 1) (by simp) with h7482 | h7482
                        · rcases p7480_3 (m.d 1 2) (by simp) with h7483 | h7483
                          · linarith only [h7483, hlam, p7480_0]
                          · rcases p7480_3 (m.d 1 3) (by simp) with h7485 | h7485
                            · linarith only [h1, h7485, hlam]
                            · rcases p7480_3 (m.d 1 4) (by simp) with h7487 | h7487
                              · linarith only [h2, h7487, hlam]
                              · rcases p7480_3 (m.d 1 5) (by simp) with h7489 | h7489
                                · linarith only [h3, h7489, hlam]
                                · rcases h3bigk with h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c | h7491c
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h6193, h7, h7464, h7479, hc23, hc34, hlam, hphi, p7491_1]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h6193, h7, h7479, hc23, hc34, hlam, hphi, p7491_1]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h7, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h5823, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h1, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h1, h6193, h7, h7479, hc23, hc34, hlam, hphi, p7491_1]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h7467, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h7469, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h4, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h7464, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h7473, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h7475, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    rcases p7491_3 (m.d 0 3) (by simp) with h7507 | h7507
                                    · linarith only [h7507, hlam, p7491_0]
                                    · rcases p7491_3 (m.d 1 3) (by simp) with h7509 | h7509
                                      · linarith only [h7467, h7509, hlam]
                                      · rcases p7491_3 (m.d 2 3) (by simp) with h7511 | h7511
                                        · linarith only [h7473, h7511, hlam]
                                        · rcases p7491_3 (m.d 3 4) (by simp) with h7513 | h7513
                                          · rcases p7491_3 (m.d 3 5) (by simp) with h7514 | h7514
                                            · linarith only [h7479, h7514, hlam]
                                            · linarith only [h5823, h7514, hlam]
                                          · linarith only [h7513, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    rcases p7491_3 (m.d 0 3) (by simp) with h7518 | h7518
                                    · linarith only [h7, h7518, hlam]
                                    · linarith only [h1, h7518, hlam]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    rcases p7491_3 (m.d 0 3) (by simp) with h7521 | h7521
                                    · linarith only [h7, h7521, hlam]
                                    · linarith only [h4, h7521, hlam]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h6193, h7, h7479, hc03, hc34, hlam, hphi, p7491_1]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    rcases p7491_3 (m.d 0 3) (by simp) with h7526 | h7526
                                    · linarith only [h7526, hlam, p7491_0]
                                    · rcases p7491_3 (m.d 1 3) (by simp) with h7528 | h7528
                                      · linarith only [h7469, h7528, hlam]
                                      · rcases p7491_3 (m.d 2 3) (by simp) with h7530 | h7530
                                        · linarith only [h7475, h7530, hlam]
                                        · rcases p7491_3 (m.d 3 4) (by simp) with h7532 | h7532
                                          · rcases p7491_3 (m.d 3 5) (by simp) with h7533 | h7533
                                            · rcases h5bigk with h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c | h7534c
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [hlam, p7534_0]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h6193, h7464, h7469, hc23, hc45, hlam, hphi, ht34, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h6193, h7475, hc23, hc45, hlam, hphi, ht34, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h5823, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h6193, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h3, hlam, p7534_0]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [hlam, p7534_0]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7469, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7471, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h6, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7466, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [hlam, p7534_0]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7475, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7477, hlam, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h1, h5823, h7464, hc23, hc35, hlam, hphi, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7464, h7469, hc23, hc35, hlam, hphi, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7475, hc23, hc35, hlam, hphi, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [hlam, p7534_0]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h1, h6193, h7, h7464, h7479, hc23, hc34, hlam, hphi, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h1, h6193, h7, h7464, hc23, hc45, hlam, hphi, ht34, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7471, hc14, hc45, hlam, hphi, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7473, h7477, hc23, hc45, hlam, hphi, ht34, p7534_1]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [h7479, hlam, p7534_0]
                                              · have p7534_0 := h7534c.1
                                                have p7534_1 := h7534c.2.1
                                                have p7534_2 := h7534c.2.2.1
                                                have p7534_3 := h7534c.2.2.2
                                                linarith only [hlam, p7534_0]
                                            · linarith only [h7533, hlam, p7491_0]
                                          · linarith only [h7, h7532, hlam]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    rcases p7491_3 (m.d 0 3) (by simp) with h7562 | h7562
                                    · linarith only [h5823, h7562, hlam]
                                    · linarith only [h1, h7562, hlam]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    rcases p7491_3 (m.d 0 3) (by simp) with h7565 | h7565
                                    · linarith only [h5823, h7565, hlam]
                                    · linarith only [h4, h7565, hlam]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [h7479, hlam, p7491_0]
                                  · have p7491_0 := h7491c.1
                                    have p7491_1 := h7491c.2.1
                                    have p7491_2 := h7491c.2.2.1
                                    have p7491_3 := h7491c.2.2.2
                                    linarith only [hlam, p7491_0]
                        · linarith only [h7482, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        rcases p7480_3 (m.d 0 1) (by simp) with h7571 | h7571
                        · rcases p7480_3 (m.d 1 2) (by simp) with h7572 | h7572
                          · linarith only [h0, h7572, hlam]
                          · linarith only [h7464, h7572, hlam]
                        · linarith only [h7571, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        rcases p7480_3 (m.d 0 1) (by simp) with h7576 | h7576
                        · rcases p7480_3 (m.d 1 2) (by simp) with h7577 | h7577
                          · linarith only [h0, h7577, hlam]
                          · linarith only [h7465, h7577, hlam]
                        · linarith only [h7576, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        rcases p7480_3 (m.d 0 1) (by simp) with h7581 | h7581
                        · rcases p7480_3 (m.d 1 2) (by simp) with h7582 | h7582
                          · linarith only [h0, h7582, hlam]
                          · linarith only [h7466, h7582, hlam]
                        · linarith only [h7581, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h0, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        rcases p7480_3 (m.d 0 1) (by simp) with h7588 | h7588
                        · rcases p7480_3 (m.d 1 2) (by simp) with h7589 | h7589
                          · rcases p7480_3 (m.d 1 3) (by simp) with h7590 | h7590
                            · linarith only [h7464, h7590, hlam]
                            · rcases p7480_3 (m.d 1 4) (by simp) with h7592 | h7592
                              · linarith only [h7465, h7592, hlam]
                              · linarith only [h7467, h7592, hlam]
                          · linarith only [h7464, h7589, hlam]
                        · linarith only [h1, h7588, hlam]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        rcases p7480_3 (m.d 0 1) (by simp) with h7597 | h7597
                        · rcases p7480_3 (m.d 1 2) (by simp) with h7598 | h7598
                          · rcases p7480_3 (m.d 1 3) (by simp) with h7599 | h7599
                            · linarith only [h7464, h7599, hlam]
                            · rcases p7480_3 (m.d 1 4) (by simp) with h7601 | h7601
                              · linarith only [h7465, h7601, hlam]
                              · rcases p7480_3 (m.d 1 5) (by simp) with h7603 | h7603
                                · linarith only [h7466, h7603, hlam]
                                · linarith only [h7471, h7603, hlam]
                          · linarith only [h7465, h7598, hlam]
                        · linarith only [h2, h7597, hlam]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        rcases p7480_3 (m.d 0 1) (by simp) with h7608 | h7608
                        · rcases p7480_3 (m.d 1 2) (by simp) with h7609 | h7609
                          · rcases p7480_3 (m.d 1 3) (by simp) with h7610 | h7610
                            · linarith only [h7464, h7610, hlam]
                            · rcases p7480_3 (m.d 1 4) (by simp) with h7612 | h7612
                              · linarith only [h7465, h7612, hlam]
                              · rcases p7480_3 (m.d 1 5) (by simp) with h7614 | h7614
                                · linarith only [h7466, h7614, hlam]
                                · rcases h3bigk with h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c | h7616c
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7, h7464, hc23, hc34, hlam, hphi, p7616_1]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7, hc23, hc34, hlam, hphi, p7616_1]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h5823, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h1, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h0, h7467, h7471, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7480_1, p7616_1]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7467, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7469, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h4, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7464, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7473, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7475, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    rcases p7616_3 (m.d 0 3) (by simp) with h7632 | h7632
                                    · linarith only [h7632, hlam, p7616_0]
                                    · rcases p7616_3 (m.d 1 3) (by simp) with h7634 | h7634
                                      · linarith only [h7467, h7634, hlam]
                                      · rcases p7616_3 (m.d 2 3) (by simp) with h7636 | h7636
                                        · linarith only [h7473, h7636, hlam]
                                        · rcases p7616_3 (m.d 3 4) (by simp) with h7638 | h7638
                                          · rcases p7616_3 (m.d 3 5) (by simp) with h7639 | h7639
                                            · linarith only [h7479, h7639, hlam]
                                            · linarith only [h5823, h7639, hlam]
                                          · linarith only [h7638, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    rcases p7616_3 (m.d 0 3) (by simp) with h7643 | h7643
                                    · linarith only [h7, h7643, hlam]
                                    · linarith only [h1, h7643, hlam]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    rcases p7616_3 (m.d 0 3) (by simp) with h7646 | h7646
                                    · linarith only [h7, h7646, hlam]
                                    · linarith only [h4, h7646, hlam]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h5823, hc03, hc34, hlam, hphi, p7616_1]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    rcases p7616_3 (m.d 0 3) (by simp) with h7651 | h7651
                                    · linarith only [h7651, hlam, p7616_0]
                                    · rcases p7616_3 (m.d 1 3) (by simp) with h7653 | h7653
                                      · linarith only [h7469, h7653, hlam]
                                      · rcases p7616_3 (m.d 2 3) (by simp) with h7655 | h7655
                                        · linarith only [h7475, h7655, hlam]
                                        · rcases p7616_3 (m.d 3 4) (by simp) with h7657 | h7657
                                          · rcases p7616_3 (m.d 3 5) (by simp) with h7658 | h7658
                                            · rcases h5bigk with h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c | h7659c
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [hlam, p7659_0]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h6193, h7471, h7479, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h6193, h7473, h7477, h7479, hc23, hc34, hlam, hphi, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h5823, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h6193, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h3, hlam, p7659_0]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [hlam, p7659_0]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h0, h7473, h7477, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7480_1, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7469, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7471, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h6, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7466, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [hlam, p7659_0]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7475, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7477, hlam, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h6, h7473, h7477, hc23, hc35, hlam, hphi, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7466, h7473, h7477, hc23, hc35, hlam, hphi, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7473, h7477, hc23, hc35, hlam, hphi, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [hlam, p7659_0]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h2, h6193, h7465, h7473, h7479, hc23, hc34, hlam, hphi, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h2, h6193, h7465, h7473, hc23, hc45, hlam, hphi, ht34, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7466, h7473, h7477, hc23, hc45, hlam, hphi, ht34, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7473, h7477, hc23, hc45, hlam, hphi, ht34, p7659_1]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [h7479, hlam, p7659_0]
                                              · have p7659_0 := h7659c.1
                                                have p7659_1 := h7659c.2.1
                                                have p7659_2 := h7659c.2.2.1
                                                have p7659_3 := h7659c.2.2.2
                                                linarith only [hlam, p7659_0]
                                            · linarith only [h7658, hlam, p7616_0]
                                          · linarith only [h7, h7657, hlam]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    rcases p7616_3 (m.d 0 3) (by simp) with h7687 | h7687
                                    · linarith only [h5823, h7687, hlam]
                                    · linarith only [h1, h7687, hlam]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    rcases p7616_3 (m.d 0 3) (by simp) with h7690 | h7690
                                    · linarith only [h5823, h7690, hlam]
                                    · linarith only [h4, h7690, hlam]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [h7479, hlam, p7616_0]
                                  · have p7616_0 := h7616c.1
                                    have p7616_1 := h7616c.2.1
                                    have p7616_2 := h7616c.2.2.1
                                    have p7616_3 := h7616c.2.2.2
                                    linarith only [hlam, p7616_0]
                          · linarith only [h7466, h7609, hlam]
                        · linarith only [h3, h7608, hlam]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h1, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h7464, hlam, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h7467, hlam, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h7469, hlam, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h2, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h7465, hlam, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h2, h6193, h7464, h7479, hc23, hc34, hlam, hphi, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h7471, hlam, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h3, hlam, p7480_0]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h7466, hlam, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h3, h6193, h7464, h7479, hc23, hc34, hlam, hphi, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [h3, h6193, h7465, h7473, h7479, hc23, hc34, hlam, hphi, p7480_1]
                      · have p7480_0 := h7480c.1
                        have p7480_1 := h7480c.2.1
                        have p7480_2 := h7480c.2.2.1
                        have p7480_3 := h7480c.2.2.2
                        linarith only [hlam, p7480_0]
                    · rcases h1bigk with h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c | h7712c
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7714 | h7714
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7715 | h7715
                          · linarith only [h7715, hlam, p7712_0]
                          · rcases p7712_3 (m.d 1 3) (by simp) with h7717 | h7717
                            · linarith only [h1, h7717, hlam]
                            · rcases p7712_3 (m.d 1 4) (by simp) with h7719 | h7719
                              · linarith only [h2, h7719, hlam]
                              · rcases p7712_3 (m.d 1 5) (by simp) with h7721 | h7721
                                · linarith only [h3, h7721, hlam]
                                · rcases h3bigk with h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c | h7723c
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7, h7464, hc23, hc34, hlam, hphi, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7, h7479, hc23, hc45, hlam, hphi, ht34, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h5823, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h1, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h1, h7, h7479, hc23, hc45, hlam, hphi, ht34, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7467, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7469, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h4, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7464, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7473, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7475, hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7479, hc03, hc45, hlam, hphi, ht34, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7479, hc13, hc45, hlam, hphi, ht34, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7479, hc23, hc45, hlam, hphi, ht34, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [hlam, p7723_0]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h7479, hlam, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    rcases p7723_3 (m.d 0 3) (by simp) with h7744 | h7744
                                    · linarith only [h7744, hlam, p7723_0]
                                    · rcases p7723_3 (m.d 1 3) (by simp) with h7746 | h7746
                                      · linarith only [h7469, h7746, hlam]
                                      · rcases p7723_3 (m.d 2 3) (by simp) with h7748 | h7748
                                        · linarith only [h7475, h7748, hlam]
                                        · rcases p7723_3 (m.d 3 4) (by simp) with h7750 | h7750
                                          · linarith only [h7479, h7750, hlam]
                                          · linarith only [h7, h7750, hlam]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    rcases p7723_3 (m.d 0 3) (by simp) with h7753 | h7753
                                    · linarith only [h5823, h7753, hlam]
                                    · linarith only [h1, h7753, hlam]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    rcases p7723_3 (m.d 0 3) (by simp) with h7756 | h7756
                                    · linarith only [h5823, h7756, hlam]
                                    · linarith only [h4, h7756, hlam]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [h1, h7, h7464, hc23, hc35, hlam, hphi, p7723_1]
                                  · have p7723_0 := h7723c.1
                                    have p7723_1 := h7723c.2.1
                                    have p7723_2 := h7723c.2.2.1
                                    have p7723_3 := h7723c.2.2.2
                                    linarith only [hlam, p7723_0]
                        · linarith only [h7714, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7762 | h7762
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7763 | h7763
                          · linarith only [h0, h7763, hlam]
                          · linarith only [h7464, h7763, hlam]
                        · linarith only [h7762, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7767 | h7767
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7768 | h7768
                          · linarith only [h0, h7768, hlam]
                          · linarith only [h7465, h7768, hlam]
                        · linarith only [h7767, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7772 | h7772
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7773 | h7773
                          · linarith only [h0, h7773, hlam]
                          · linarith only [h7466, h7773, hlam]
                        · linarith only [h7772, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h0, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7779 | h7779
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7780 | h7780
                          · rcases p7712_3 (m.d 1 3) (by simp) with h7781 | h7781
                            · linarith only [h7464, h7781, hlam]
                            · rcases p7712_3 (m.d 1 4) (by simp) with h7783 | h7783
                              · linarith only [h7465, h7783, hlam]
                              · linarith only [h7467, h7783, hlam]
                          · linarith only [h7464, h7780, hlam]
                        · linarith only [h1, h7779, hlam]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7788 | h7788
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7789 | h7789
                          · rcases p7712_3 (m.d 1 3) (by simp) with h7790 | h7790
                            · linarith only [h7464, h7790, hlam]
                            · rcases p7712_3 (m.d 1 4) (by simp) with h7792 | h7792
                              · linarith only [h7465, h7792, hlam]
                              · rcases p7712_3 (m.d 1 5) (by simp) with h7794 | h7794
                                · linarith only [h7466, h7794, hlam]
                                · linarith only [h7471, h7794, hlam]
                          · linarith only [h7465, h7789, hlam]
                        · linarith only [h2, h7788, hlam]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7799 | h7799
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7800 | h7800
                          · rcases p7712_3 (m.d 1 3) (by simp) with h7801 | h7801
                            · linarith only [h7464, h7801, hlam]
                            · rcases p7712_3 (m.d 1 4) (by simp) with h7803 | h7803
                              · linarith only [h7465, h7803, hlam]
                              · rcases p7712_3 (m.d 1 5) (by simp) with h7805 | h7805
                                · linarith only [h7466, h7805, hlam]
                                · rcases h3bigk with h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c | h7807c
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7, hc13, hc34, hlam, hphi, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7, hc23, hc34, hlam, hphi, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h5823, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h1, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h0, h7467, h7471, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7712_1, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7467, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7469, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h4, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7464, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7473, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7475, hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7479, hc03, hc45, hlam, hphi, ht34, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7464, h7479, hc23, hc45, hlam, hphi, ht34, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7479, hc23, hc45, hlam, hphi, ht34, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [hlam, p7807_0]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h7479, hlam, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    rcases p7807_3 (m.d 0 3) (by simp) with h7828 | h7828
                                    · linarith only [h7828, hlam, p7807_0]
                                    · rcases p7807_3 (m.d 1 3) (by simp) with h7830 | h7830
                                      · linarith only [h7469, h7830, hlam]
                                      · rcases p7807_3 (m.d 2 3) (by simp) with h7832 | h7832
                                        · linarith only [h7475, h7832, hlam]
                                        · rcases p7807_3 (m.d 3 4) (by simp) with h7834 | h7834
                                          · linarith only [h7479, h7834, hlam]
                                          · linarith only [h7, h7834, hlam]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    rcases p7807_3 (m.d 0 3) (by simp) with h7837 | h7837
                                    · linarith only [h5823, h7837, hlam]
                                    · linarith only [h1, h7837, hlam]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    rcases p7807_3 (m.d 0 3) (by simp) with h7840 | h7840
                                    · linarith only [h5823, h7840, hlam]
                                    · linarith only [h4, h7840, hlam]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [h1, h7, h7464, h7479, hc23, hc45, hlam, hphi, ht34, p7807_1]
                                  · have p7807_0 := h7807c.1
                                    have p7807_1 := h7807c.2.1
                                    have p7807_2 := h7807c.2.2.1
                                    have p7807_3 := h7807c.2.2.2
                                    linarith only [hlam, p7807_0]
                          · linarith only [h7466, h7800, hlam]
                        · linarith only [h3, h7799, hlam]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h1, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h7464, hlam, p7712_1]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h7467, hlam, p7712_1]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h7469, hlam, p7712_1]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h2, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h7465, hlam, p7712_1]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h2, h6193, h7464, hc23, hc45, hlam, hphi, ht34, p7712_1]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h7471, hlam, p7712_1]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h3, hlam, p7712_0]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [h7466, hlam, p7712_1]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7859 | h7859
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7860 | h7860
                          · rcases p7712_3 (m.d 1 3) (by simp) with h7861 | h7861
                            · linarith only [h7469, h7861, hlam]
                            · rcases p7712_3 (m.d 1 4) (by simp) with h7863 | h7863
                              · linarith only [h7471, h7863, hlam]
                              · linarith only [h7467, h7863, hlam]
                          · linarith only [h7464, h7860, hlam]
                        · linarith only [h1, h7859, hlam]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        rcases p7712_3 (m.d 0 1) (by simp) with h7868 | h7868
                        · rcases p7712_3 (m.d 1 2) (by simp) with h7869 | h7869
                          · rcases p7712_3 (m.d 1 3) (by simp) with h7870 | h7870
                            · linarith only [h7469, h7870, hlam]
                            · rcases p7712_3 (m.d 1 4) (by simp) with h7872 | h7872
                              · linarith only [h7471, h7872, hlam]
                              · rcases p7712_3 (m.d 1 5) (by simp) with h7874 | h7874
                                · rcases h3bigk with h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7, h7464, h7479, hc23, hc45, hlam, hphi, ht34, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7, h7479, hc23, hc45, hlam, hphi, ht34, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h5823, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h1, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h1, h7, h7479, hc23, hc45, hlam, hphi, ht34, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7467, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7469, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h4, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7464, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7473, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7475, hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7479, hc03, hc45, hlam, hphi, ht34, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7464, h7479, hc23, hc45, hlam, hphi, ht34, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7479, hc23, hc45, hlam, hphi, ht34, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [hlam, p7875_0]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h7479, hlam, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    rcases p7875_3 (m.d 0 3) (by simp) with h7896 | h7896
                                    · linarith only [h7896, hlam, p7875_0]
                                    · rcases p7875_3 (m.d 1 3) (by simp) with h7898 | h7898
                                      · linarith only [h7469, h7898, hlam]
                                      · rcases p7875_3 (m.d 2 3) (by simp) with h7900 | h7900
                                        · linarith only [h7475, h7900, hlam]
                                        · rcases p7875_3 (m.d 3 4) (by simp) with h7902 | h7902
                                          · linarith only [h7479, h7902, hlam]
                                          · linarith only [h7, h7902, hlam]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    rcases p7875_3 (m.d 0 3) (by simp) with h7905 | h7905
                                    · linarith only [h5823, h7905, hlam]
                                    · linarith only [h1, h7905, hlam]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    rcases p7875_3 (m.d 0 3) (by simp) with h7908 | h7908
                                    · linarith only [h5823, h7908, hlam]
                                    · linarith only [h4, h7908, hlam]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [h1, h7, h7464, h7479, hc23, hc45, hlam, hphi, ht34, p7875_1]
                                  · have p7875_0 := h7875c.1
                                    have p7875_1 := h7875c.2.1
                                    have p7875_2 := h7875c.2.2.1
                                    have p7875_3 := h7875c.2.2.2
                                    linarith only [hlam, p7875_0]
                                · linarith only [h7471, h7874, hlam]
                          · linarith only [h7465, h7869, hlam]
                        · linarith only [h2, h7868, hlam]
                      · have p7712_0 := h7712c.1
                        have p7712_1 := h7712c.2.1
                        have p7712_2 := h7712c.2.2.1
                        have p7712_3 := h7712c.2.2.2
                        linarith only [hlam, p7712_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h7917 | h7917
        · linarith only [h1, h7, h7917, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h7919 | h7919
          · linarith only [h1, h5823, h6, h7, h7466, h7919, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7921 | h7921
            · linarith only [h2, h6193, h7921, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7923 | h7923
              · linarith only [h1, h7, h7464, h7923, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7925 | h7925
                · linarith only [h1, h5823, h6, h7, h7464, h7466, h7925, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7927 | h7927
                  · linarith only [h6, h6193, h7, h7465, h7466, h7927, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7929 | h7929
                    · linarith only [h6, h6193, h7464, h7466, h7929, hc23, hc34, hlam, hphi]
                    · rcases h1bigk with h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c | h7931c
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        rcases p7931_3 (m.d 0 1) (by simp) with h7933 | h7933
                        · rcases p7931_3 (m.d 1 2) (by simp) with h7934 | h7934
                          · linarith only [h7934, hlam, p7931_0]
                          · rcases p7931_3 (m.d 1 3) (by simp) with h7936 | h7936
                            · linarith only [h1, h7936, hlam]
                            · rcases p7931_3 (m.d 1 4) (by simp) with h7938 | h7938
                              · linarith only [h2, h7938, hlam]
                              · rcases p7931_3 (m.d 1 5) (by simp) with h7940 | h7940
                                · linarith only [h3, h7940, hlam]
                                · linarith only [h7466, h7940, hlam]
                        · linarith only [h7933, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        rcases p7931_3 (m.d 0 1) (by simp) with h7944 | h7944
                        · rcases p7931_3 (m.d 1 2) (by simp) with h7945 | h7945
                          · linarith only [h0, h7945, hlam]
                          · linarith only [h7464, h7945, hlam]
                        · linarith only [h7944, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        rcases p7931_3 (m.d 0 1) (by simp) with h7949 | h7949
                        · rcases p7931_3 (m.d 1 2) (by simp) with h7950 | h7950
                          · linarith only [h0, h7950, hlam]
                          · linarith only [h7465, h7950, hlam]
                        · linarith only [h7949, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        rcases p7931_3 (m.d 0 1) (by simp) with h7954 | h7954
                        · rcases p7931_3 (m.d 1 2) (by simp) with h7955 | h7955
                          · linarith only [h0, h7955, hlam]
                          · rcases p7931_3 (m.d 1 3) (by simp) with h7957 | h7957
                            · linarith only [h1, h7957, hlam]
                            · rcases p7931_3 (m.d 1 4) (by simp) with h7959 | h7959
                              · linarith only [h2, h7959, hlam]
                              · rcases p7931_3 (m.d 1 5) (by simp) with h7961 | h7961
                                · linarith only [h7961, hlam, p7931_0]
                                · rcases h3bigk with h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c | h7963c
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7, h7929, hc13, hc45, hlam, hphi, ht34, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7, h7929, hc23, hc45, hlam, hphi, ht34, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h5823, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h1, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h1, h7, h7929, hc23, hc45, hlam, hphi, ht34, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7917, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7919, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h4, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7464, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7923, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7925, hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7929, hc03, hc45, hlam, hphi, ht34, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7929, hc13, hc45, hlam, hphi, ht34, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7929, hc23, hc45, hlam, hphi, ht34, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [hlam, p7963_0]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7929, hlam, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    rcases p7963_3 (m.d 0 3) (by simp) with h7984 | h7984
                                    · linarith only [h7984, hlam, p7963_0]
                                    · rcases p7963_3 (m.d 1 3) (by simp) with h7986 | h7986
                                      · linarith only [h7919, h7986, hlam]
                                      · rcases p7963_3 (m.d 2 3) (by simp) with h7988 | h7988
                                        · linarith only [h7925, h7988, hlam]
                                        · rcases p7963_3 (m.d 3 4) (by simp) with h7990 | h7990
                                          · linarith only [h7929, h7990, hlam]
                                          · linarith only [h7, h7990, hlam]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    rcases p7963_3 (m.d 0 3) (by simp) with h7993 | h7993
                                    · linarith only [h5823, h7993, hlam]
                                    · linarith only [h1, h7993, hlam]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    rcases p7963_3 (m.d 0 3) (by simp) with h7996 | h7996
                                    · linarith only [h5823, h7996, hlam]
                                    · linarith only [h4, h7996, hlam]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [h7, h7929, hc03, hc45, hlam, hphi, ht34, p7963_1]
                                  · have p7963_0 := h7963c.1
                                    have p7963_1 := h7963c.2.1
                                    have p7963_2 := h7963c.2.2.1
                                    have p7963_3 := h7963c.2.2.2
                                    linarith only [hlam, p7963_0]
                        · linarith only [h7954, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h0, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h0, h6, h7464, h7466, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h0, h6, h7466, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h7466, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h1, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h7464, hlam, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h7917, hlam, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h7919, hlam, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h2, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h7465, hlam, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h2, h6193, h7464, hc23, hc45, hlam, hphi, ht34, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h7921, hlam, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h3, hlam, p7931_0]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [h3, h5823, h7464, h7929, hc23, hc45, hlam, hphi, ht34, p7931_1]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        rcases p7931_3 (m.d 0 1) (by simp) with h8019 | h8019
                        · rcases p7931_3 (m.d 1 2) (by simp) with h8020 | h8020
                          · linarith only [h7466, h8020, hlam]
                          · linarith only [h7464, h8020, hlam]
                        · linarith only [h1, h8019, hlam]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        rcases p7931_3 (m.d 0 1) (by simp) with h8024 | h8024
                        · rcases p7931_3 (m.d 1 2) (by simp) with h8025 | h8025
                          · linarith only [h7466, h8025, hlam]
                          · linarith only [h7465, h8025, hlam]
                        · linarith only [h2, h8024, hlam]
                      · have p7931_0 := h7931c.1
                        have p7931_1 := h7931c.2.1
                        have p7931_2 := h7931c.2.2.1
                        have p7931_3 := h7931c.2.2.2
                        linarith only [hlam, p7931_0]
    · linarith only [h5, h6193, h7464, h7465, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8031 | h8031
    · linarith only [h4, h6193, h7, h7464, h8031, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8033 | h8033
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8034 | h8034
        · linarith only [h4, h7, h7464, h8034, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8036 | h8036
          · linarith only [h4, h5823, h7464, h8036, hlam]
          · linarith only [h7464, h8033, h8036, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8039 | h8039
        · linarith only [h1, h7, h8039, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8041 | h8041
          · linarith only [h1, h4, h5823, h7464, h8041, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8043 | h8043
            · linarith only [h2, h6193, h8043, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8045 | h8045
              · linarith only [h4, h7, h8045, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8047 | h8047
                · linarith only [h4, h5823, h8047, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8049 | h8049
                  · linarith only [h5, h6193, h8049, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8051 | h8051
                    · linarith only [h4, h6193, h7, h7464, h8051, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h7, h7464, h8051, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h6193 | h6193
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823 h6193
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823 h6193

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h5823 | h5823
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

set_option maxHeartbeats 16390000 in
set_option maxHeartbeats 16390000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h8054 | h8054
    · rcases m.htr 0 3 5 (by decide) (by decide) with h8055 | h8055
      · linarith only [h4, h6, h8055, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8057 | h8057
        · linarith only [h5, h6, h8057, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h8059 | h8059
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8060 | h8060
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8061 | h8061
              · linarith only [h0, h4, h6, h8054, h8061, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8063 | h8063
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8064 | h8064
                  · linarith only [h1, h8055, h8064, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h8066 | h8066
                    · linarith only [h2, h8057, h8066, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h8068 | h8068
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h8069 | h8069
                        · linarith only [h0, h6, h8055, h8059, h8069, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h8071 | h8071
                          · linarith only [h0, h2, h6, h8057, h8059, h8060, h8068, h8071, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h6, h8059, h8068, h8071, hc34, hc45, hlam, hphi]
                      · linarith only [h8054, h8055, h8068, hc23, hc35, hlam, hphi]
                · linarith only [h8054, h8055, h8059, h8063, hc23, hc35, hlam, hphi]
            · linarith only [h5, h6, h8060, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h8059, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h8078 | h8078
      · linarith only [h5, h6, h8054, h8078, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8080 | h8080
        · linarith only [h5, h6, h8080, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h8082 | h8082
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8083 | h8083
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8084 | h8084
              · linarith only [h0, h6, h8084, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8086 | h8086
                · linarith only [h1, h8054, h8086, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8088 | h8088
                  · linarith only [h1, h4, h6, h8054, h8078, h8088, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h8090 | h8090
                    · linarith only [h2, h8080, h8090, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h8092 | h8092
                      · linarith only [h0, h6, h8054, h8082, h8092, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h8094 | h8094
                        · linarith only [h4, h6, h8078, h8094, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h8096 | h8096
                          · linarith only [h0, h1, h6, h8054, h8080, h8083, h8096, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h8098 | h8098
                            · linarith only [h4, h6, h8096, h8098, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c | h8100c
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                rcases p8100_3 (m.d 0 1) (by simp) with h8102 | h8102
                                · rcases p8100_3 (m.d 1 2) (by simp) with h8103 | h8103
                                  · linarith only [h8103, hlam, p8100_0]
                                  · rcases p8100_3 (m.d 1 3) (by simp) with h8105 | h8105
                                    · linarith only [h1, h8105, hlam]
                                    · rcases p8100_3 (m.d 1 4) (by simp) with h8107 | h8107
                                      · linarith only [h2, h8107, hlam]
                                      · rcases p8100_3 (m.d 1 5) (by simp) with h8109 | h8109
                                        · linarith only [h3, h8109, hlam]
                                        · linarith only [h8084, h8109, hlam]
                                · linarith only [h8102, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                rcases p8100_3 (m.d 0 1) (by simp) with h8113 | h8113
                                · rcases p8100_3 (m.d 1 2) (by simp) with h8114 | h8114
                                  · linarith only [h0, h8114, hlam]
                                  · linarith only [h8082, h8114, hlam]
                                · linarith only [h8113, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                rcases p8100_3 (m.d 0 1) (by simp) with h8118 | h8118
                                · rcases p8100_3 (m.d 1 2) (by simp) with h8119 | h8119
                                  · linarith only [h0, h8119, hlam]
                                  · linarith only [h8083, h8119, hlam]
                                · linarith only [h8118, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                rcases p8100_3 (m.d 0 1) (by simp) with h8123 | h8123
                                · rcases p8100_3 (m.d 1 2) (by simp) with h8124 | h8124
                                  · linarith only [h0, h8124, hlam]
                                  · rcases p8100_3 (m.d 1 3) (by simp) with h8126 | h8126
                                    · linarith only [h1, h8126, hlam]
                                    · rcases p8100_3 (m.d 1 4) (by simp) with h8128 | h8128
                                      · linarith only [h2, h8128, hlam]
                                      · rcases p8100_3 (m.d 1 5) (by simp) with h8130 | h8130
                                        · linarith only [h8130, hlam, p8100_0]
                                        · rcases h3bigk with h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h4, h6, h8082, h8094, hc23, hc35, hlam, hphi, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h4, h6, h8094, h8098, hc23, hc45, hlam, hphi, ht34, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8054, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8078, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h1, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h1, h4, h6, h8094, h8098, hc23, hc45, hlam, hphi, ht34, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8086, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8088, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h4, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8082, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8092, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8094, hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8098, hc03, hc45, hlam, hphi, ht34, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8082, h8098, hc23, hc45, hlam, hphi, ht34, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8098, hc23, hc45, hlam, hphi, ht34, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [hlam, p8132_0]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h8098, hlam, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            rcases p8132_3 (m.d 0 3) (by simp) with h8153 | h8153
                                            · linarith only [h8153, hlam, p8132_0]
                                            · rcases p8132_3 (m.d 1 3) (by simp) with h8155 | h8155
                                              · linarith only [h8088, h8155, hlam]
                                              · rcases p8132_3 (m.d 2 3) (by simp) with h8157 | h8157
                                                · linarith only [h8094, h8157, hlam]
                                                · rcases p8132_3 (m.d 3 4) (by simp) with h8159 | h8159
                                                  · linarith only [h8098, h8159, hlam]
                                                  · linarith only [h8054, h8159, hlam]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            rcases p8132_3 (m.d 0 3) (by simp) with h8162 | h8162
                                            · linarith only [h8078, h8162, hlam]
                                            · linarith only [h1, h8162, hlam]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            rcases p8132_3 (m.d 0 3) (by simp) with h8165 | h8165
                                            · linarith only [h8078, h8165, hlam]
                                            · linarith only [h4, h8165, hlam]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [h1, h8054, h8082, h8098, hc23, hc45, hlam, hphi, ht34, p8132_1]
                                          · have p8132_0 := h8132c.1
                                            have p8132_1 := h8132c.2.1
                                            have p8132_2 := h8132c.2.2.1
                                            have p8132_3 := h8132c.2.2.2
                                            linarith only [hlam, p8132_0]
                                · linarith only [h8123, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h0, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h0, h6, h8082, h8094, h8098, hc23, hc45, hlam, hphi, ht34, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h0, h6, h8094, h8098, hc14, hc45, hlam, hphi, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h8084, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h1, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h8082, hlam, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h8086, hlam, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h8088, hlam, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h2, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h8083, hlam, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h2, h5, h6, h8082, h8094, h8098, hc23, hc45, hlam, hphi, ht34, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h8090, hlam, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h3, hlam, p8100_0]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [h3, h8083, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p8100_1]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                rcases p8100_3 (m.d 0 1) (by simp) with h8188 | h8188
                                · rcases p8100_3 (m.d 1 2) (by simp) with h8189 | h8189
                                  · linarith only [h8084, h8189, hlam]
                                  · linarith only [h8082, h8189, hlam]
                                · linarith only [h1, h8188, hlam]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                rcases p8100_3 (m.d 0 1) (by simp) with h8193 | h8193
                                · rcases p8100_3 (m.d 1 2) (by simp) with h8194 | h8194
                                  · linarith only [h8084, h8194, hlam]
                                  · linarith only [h8083, h8194, hlam]
                                · linarith only [h2, h8193, hlam]
                              · have p8100_0 := h8100c.1
                                have p8100_1 := h8100c.2.1
                                have p8100_2 := h8100c.2.2.1
                                have p8100_3 := h8100c.2.2.2
                                linarith only [hlam, p8100_0]
            · linarith only [h5, h6, h8083, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h8082, hc12, hc25, hlam, hphi]

end R2N4
