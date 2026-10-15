import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7678000 in
set_option maxHeartbeats 7678000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s8 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h6421 := hg6421
  rcases m.htr 0 1 4 (by decide) (by decide) with h7464 | h7464
  · rcases m.htr 0 1 5 (by decide) (by decide) with h7465 | h7465
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7466 | h7466
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7467 | h7467
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7468 | h7468
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7469 | h7469
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7470 | h7470
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7471 | h7471
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7472 | h7472
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7473 | h7473
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7474 | h7474
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7475 | h7475
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7476 | h7476
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7477 | h7477
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7478 | h7478
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7479 | h7479
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7480 | h7480
                                  · rcases h0bigk with h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h0, hlam, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h6421, hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h6421, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h6421, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h0, h6421, h7464, h7474, h7476, h7478, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h0, h7469, h7480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      rcases p7481_3 (m.d 0 1) (by simp) with h7491 | h7491
                                      · linarith only [h0, h7491, hlam]
                                      · linarith only [h7465, h7491, hlam]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7464, h7473, h7477, h7480, hc03, hc45, hlam, hphi, ht0b, ht5b, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7466, hlam, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h6421, h7464, h7472, h7473, h7477, h7480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      rcases p7481_3 (m.d 0 1) (by simp) with h7498 | h7498
                                      · linarith only [h6421, h7498, hlam]
                                      · linarith only [h7465, h7498, hlam]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7464, hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7467, hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7469, hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h0, h7464, h7465, h7474, h7478, h7480, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7465, hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7468, hlam, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7470, hlam, p7481_0]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [h7471, hlam, p7481_1]
                                    · have p7481_0 := h7481c.1
                                      have p7481_1 := h7481c.2.1
                                      have p7481_2 := h7481c.2.2.1
                                      have p7481_3 := h7481c.2.2.2
                                      linarith only [hlam, p7481_0]
                                  · linarith only [h6421, h7464, h7472, h7476, h7480, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h6421, h7464, h7472, h7476, h7477, h7479, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7513 | h7513
                                · linarith only [h7477, h7478, h7513, hlam]
                                · linarith only [h6421, h7464, h7472, h7476, h7513, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7516 | h7516
                              · linarith only [h6421, h7464, h7472, h7475, h7477, h7516, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7518 | h7518
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7519 | h7519
                                  · rcases h0bigk with h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c | h7520c
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h0, hlam, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h6421, hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h6421, h7472, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h6421, h7472, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h0, h6421, h7464, h7475, h7516, h7519, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h0, h7464, h7475, h7516, h7519, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h0, h7470, h7516, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7464, h7475, h7516, h7519, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7466, hlam, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h0, h7464, h7466, h7475, h7516, h7519, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h0, h7466, h7470, h7516, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7464, hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7467, hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7469, hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7470, h7516, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7465, hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7468, hlam, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7470, hlam, p7520_0]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [h7471, hlam, p7520_1]
                                    · have p7520_0 := h7520c.1
                                      have p7520_1 := h7520c.2.1
                                      have p7520_2 := h7520c.2.2.1
                                      have p7520_3 := h7520c.2.2.2
                                      linarith only [hlam, p7520_0]
                                  · linarith only [h6421, h7464, h7472, h7476, h7477, h7519, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h6421, h7464, h7472, h7476, h7477, h7518, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7548 | h7548
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7549 | h7549
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7550 | h7550
                                · linarith only [h7473, h7476, h7550, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7552 | h7552
                                  · linarith only [h7473, h7476, h7548, h7552, hlam]
                                  · rcases h0bigk with h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c | h7554c
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h0, hlam, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h6421, hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h6421, h7472, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h6421, h7471, h7472, h7473, h7476, h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h0, h6421, hc01, hc12, hlam, hphi, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h0, h7471, h7473, h7476, h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h0, h7471, h7473, h7476, h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7464, h7471, h7473, h7476, h7548, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7466, hlam, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h6421, h7471, h7472, h7473, h7476, h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h6421, h7471, h7472, h7473, h7476, h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7464, hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7467, hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7469, hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7464, h7471, h7473, h7476, h7548, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7465, hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7468, hlam, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7470, hlam, p7554_0]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [h7471, hlam, p7554_1]
                                    · have p7554_0 := h7554c.1
                                      have p7554_1 := h7554c.2.1
                                      have p7554_2 := h7554c.2.2.1
                                      have p7554_3 := h7554c.2.2.2
                                      linarith only [hlam, p7554_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7580 | h7580
                                · linarith only [h7473, h7476, h7580, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7582 | h7582
                                  · linarith only [h7470, h7476, h7548, h7549, h7582, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h6421, h7464, h7471, h7472, h7548, h7549, h7582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h6421, h7464, h7471, h7472, h7475, h7476, h7548, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h6421, h7469, h7475, hlam]
                      · linarith only [h0, h7468, h7474, hlam]
                    · linarith only [h0, h7467, h7473, hlam]
                  · linarith only [h0, h7466, h7472, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7590 | h7590
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7591 | h7591
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7592 | h7592
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7593 | h7593
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7594 | h7594
                          · linarith only [h6421, h7464, h7471, h7590, h7594, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7596 | h7596
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7597 | h7597
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7598 | h7598
                                · linarith only [h7464, h7471, h7591, h7598, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7600 | h7600
                                  · linarith only [h7466, h7471, h7596, h7600, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h0, hlam, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h6421, hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h0, h7464, h7591, h7596, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h0, h7464, h7471, h7591, h7596, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h0, h6421, h7465, h7591, h7594, h7596, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      rcases p7602_3 (m.d 0 1) (by simp) with h7611 | h7611
                                      · linarith only [h0, h7611, hlam]
                                      · linarith only [h7464, h7611, hlam]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      rcases p7602_3 (m.d 0 1) (by simp) with h7614 | h7614
                                      · linarith only [h0, h7614, hlam]
                                      · linarith only [h7465, h7614, hlam]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7465, h7591, h7594, h7596, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7466, hlam, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      rcases p7602_3 (m.d 0 1) (by simp) with h7620 | h7620
                                      · linarith only [h6421, h7620, hlam]
                                      · linarith only [h7464, h7620, hlam]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      rcases p7602_3 (m.d 0 1) (by simp) with h7623 | h7623
                                      · linarith only [h6421, h7623, hlam]
                                      · linarith only [h7465, h7623, hlam]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7464, hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7467, hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7469, hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7471, hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7465, hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7468, hlam, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h7470, hlam, p7602_0]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [h0, h7464, h7465, h7591, h7596, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7602_1]
                                    · have p7602_0 := h7602c.1
                                      have p7602_1 := h7602c.2.1
                                      have p7602_2 := h7602c.2.2.1
                                      have p7602_3 := h7602c.2.2.2
                                      linarith only [hlam, p7602_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7636 | h7636
                                · linarith only [h6421, h7464, h7465, h7471, h7590, h7591, h7592, h7596, h7597, h7636, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7638 | h7638
                                  · linarith only [h7470, h7471, h7596, h7597, h7638, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c | h7640c
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h0, hlam, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h6421, hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h6421, h7464, h7590, h7591, h7596, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h6421, h7470, h7590, h7596, h7597, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h0, h6421, h7465, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      rcases p7640_3 (m.d 0 1) (by simp) with h7649 | h7649
                                      · linarith only [h0, h7649, hlam]
                                      · linarith only [h7464, h7649, hlam]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h0, h7470, h7596, h7597, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7465, h7470, h7596, h7597, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7466, hlam, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      rcases p7640_3 (m.d 0 1) (by simp) with h7656 | h7656
                                      · linarith only [h6421, h7656, hlam]
                                      · linarith only [h7464, h7656, hlam]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h6421, h7470, h7590, h7596, h7597, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7464, hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7467, hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7469, hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7471, hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7465, hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7468, hlam, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7470, hlam, p7640_0]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [h7464, h7471, h7591, h7596, hc34, hc45, hlam, hphi, p7640_1]
                                    · have p7640_0 := h7640c.1
                                      have p7640_1 := h7640c.2.1
                                      have p7640_2 := h7640c.2.2.1
                                      have p7640_3 := h7640c.2.2.2
                                      linarith only [hlam, p7640_0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7670 | h7670
                              · linarith only [h6421, h7465, h7590, h7593, h7594, h7596, h7670, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7672 | h7672
                                · linarith only [h7464, h7471, h7593, h7596, h7672, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7674 | h7674
                                  · linarith only [h7464, h7471, h7593, h7674, hlam]
                                  · rcases h0bigk with h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h0, hlam, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h6421, hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h6421, h7464, h7590, h7593, h7596, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h6421, h7590, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h0, h6421, h7464, h7593, h7596, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h0, h7464, h7593, h7596, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h0, h7464, h7471, h7593, h7596, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7464, h7593, h7596, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7466, hlam, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h6421, h7464, h7590, h7593, h7596, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h6421, h7464, h7471, h7590, h7593, h7596, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7464, hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7467, hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7469, hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7471, hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7465, hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7468, hlam, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7470, hlam, p7676_0]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [h7464, h7593, h7596, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7676_1]
                                    · have p7676_0 := h7676c.1
                                      have p7676_1 := h7676c.2.1
                                      have p7676_2 := h7676c.2.2.1
                                      have p7676_3 := h7676c.2.2.2
                                      linarith only [hlam, p7676_0]
                        · linarith only [h6421, h7469, h7593, hlam]
                      · linarith only [h0, h7468, h7592, hlam]
                    · linarith only [h0, h7467, h7591, hlam]
                  · linarith only [h0, h7466, h7590, hlam]
              · linarith only [h6421, h7465, h7470, hlam]
            · linarith only [h6421, h7464, h7469, hlam]
          · linarith only [h6421, h7465, h7466, h7468, hlam]
        · linarith only [h6421, h7464, h7466, h7467, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7710 | h7710
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7711 | h7711
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7712 | h7712
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7713 | h7713
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7714 | h7714
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7715 | h7715
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7716 | h7716
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7717 | h7717
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7718 | h7718
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7719 | h7719
                          · linarith only [h0, h7464, h7466, h7715, h7719, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h7464, h7466, h7714, h7715, h7719, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h6421, h7464, h7712, h7714, h7718, hc03, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h7466, h7715, h7717, hc02, hc25, hlam, hphi]
                    · linarith only [h0, h7464, h7466, h7715, h7716, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7725 | h7725
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7726 | h7726
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7727 | h7727
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7728 | h7728
                          · linarith only [h0, h7464, h7715, h7728, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h7464, h7714, h7715, h7727, h7728, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h6421, h7712, h7727, hlam]
                      · linarith only [h0, h7711, h7726, hlam]
                    · linarith only [h0, h7710, h7725, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7734 | h7734
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7735 | h7735
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7736 | h7736
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7737 | h7737
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7738 | h7738
                          · linarith only [h0, h7464, h7466, h7714, h7734, h7738, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7740 | h7740
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7741 | h7741
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7742 | h7742
                                · linarith only [h7464, h7714, h7735, h7742, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7744 | h7744
                                  · linarith only [h7464, h7714, h7735, h7740, h7744, hlam]
                                  · rcases h0bigk with h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c | h7746c
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h0, hlam, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h6421, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h0, h7464, h7466, h7734, h7735, h7740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h0, h7466, h7734, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7466, h7734, hc01, hc12, hlam, hphi, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7466, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7464, h7466, h7734, h7735, h7740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7465, h7466, h7734, h7735, h7738, h7740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7465, h7466, h7734, h7735, h7738, h7740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7466, h7734, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7464, h7466, h7734, h7735, h7740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7465, h7466, h7734, h7735, h7738, h7740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7464, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7710, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7712, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7714, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7465, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7711, hlam, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h7713, hlam, p7746_0]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [h0, h7464, h7465, h7735, h7740, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7746_1]
                                    · have p7746_0 := h7746c.1
                                      have p7746_1 := h7746c.2.1
                                      have p7746_2 := h7746c.2.2.1
                                      have p7746_3 := h7746c.2.2.2
                                      linarith only [hlam, p7746_0]
                              · linarith only [h7466, h7713, h7741, hlam]
                            · linarith only [h7466, h7712, h7740, hlam]
                        · linarith only [h6421, h7465, h7712, h7714, h7737, hlam]
                      · linarith only [h7466, h7711, h7736, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h7466, h7734, h7735, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7777 | h7777
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7778 | h7778
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7779 | h7779
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7780 | h7780
                          · linarith only [h0, h7464, h7714, h7734, h7780, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7782 | h7782
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7783 | h7783
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7784 | h7784
                                · linarith only [h7464, h7714, h7777, h7784, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7786 | h7786
                                  · linarith only [h7464, h7714, h7777, h7782, h7786, hlam]
                                  · rcases h0bigk with h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c | h7788c
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h0, hlam, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h6421, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h0, h7734, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h0, h7734, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h0, h7734, hc01, hc23, hlam, hphi, ht12, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7466, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h0, h7464, h7734, h7777, h7782, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h0, h7465, h7734, h7778, h7783, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h6421, h7464, h7734, h7777, h7782, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h6421, h7734, hc02, hc23, hlam, hphi, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      rcases p7788_3 (m.d 0 1) (by simp) with h7802 | h7802
                                      · linarith only [h6421, h7802, hlam]
                                      · linarith only [h7464, h7802, hlam]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      rcases p7788_3 (m.d 0 1) (by simp) with h7805 | h7805
                                      · linarith only [h6421, h7805, hlam]
                                      · linarith only [h7465, h7805, hlam]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7464, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7710, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7712, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7714, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7465, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7711, hlam, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h7713, hlam, p7788_0]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [h0, h7464, h7465, h7734, h7777, h7782, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7788_1]
                                    · have p7788_0 := h7788c.1
                                      have p7788_1 := h7788c.2.1
                                      have p7788_2 := h7788c.2.2.1
                                      have p7788_3 := h7788c.2.2.2
                                      linarith only [hlam, p7788_0]
                              · linarith only [h0, h7734, h7783, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h7465, h7734, h7777, h7780, h7782, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h6421, h7712, h7714, h7779, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h7464, h7711, h7777, h7778, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7710, h7777, hlam]
              · linarith only [h6421, h7465, h7713, hlam]
            · linarith only [h0, h7464, h7466, h7712, hlam]
          · linarith only [h0, h7465, h7711, hlam]
        · linarith only [h0, h7464, h7710, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7827 | h7827
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7828 | h7828
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7829 | h7829
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7830 | h7830
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7831 | h7831
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7832 | h7832
                · linarith only [h7464, h7465, h7832, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7834 | h7834
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7835 | h7835
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7836 | h7836
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7837 | h7837
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7838 | h7838
                          · linarith only [h7464, h7465, h7832, h7838, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7840 | h7840
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7841 | h7841
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7842 | h7842
                                · linarith only [h7464, h7465, h7835, h7838, h7842, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7844 | h7844
                                  · linarith only [h7465, h7827, h7838, h7840, h7844, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                  · rcases h0bigk with h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c | h7846c
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h0, hlam, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h6421, hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7465, h7838, hc04, hc45, hlam, hphi, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7465, hlam, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h0, h7464, h7465, h7831, h7835, h7840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      rcases p7846_3 (m.d 0 1) (by simp) with h7855 | h7855
                                      · linarith only [h0, h7855, hlam]
                                      · linarith only [h7464, h7855, hlam]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h0, h7464, h7465, h7835, h7840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7464, h7835, h7840, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7827, hlam, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      rcases p7846_3 (m.d 0 1) (by simp) with h7862 | h7862
                                      · linarith only [h6421, h7862, hlam]
                                      · linarith only [h7464, h7862, hlam]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h0, h7464, h7465, h7827, h7835, h7840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7464, hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7828, hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7830, hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7832, hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7464, h7835, h7840, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7829, hlam, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7831, hlam, p7846_0]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [h7464, h7832, h7835, h7840, hc34, hc45, hlam, hphi, p7846_1]
                                    · have p7846_0 := h7846c.1
                                      have p7846_1 := h7846c.2.1
                                      have p7846_2 := h7846c.2.2.1
                                      have p7846_3 := h7846c.2.2.2
                                      linarith only [hlam, p7846_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7876 | h7876
                                · linarith only [h7464, h7465, h7835, h7838, h7876, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7878 | h7878
                                  · linarith only [h7464, h7465, h7827, h7830, h7835, h7838, h7878, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c | h7880c
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h0, hlam, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h6421, hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7464, h7465, h7835, h7840, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7465, hlam, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h0, h6421, hc01, hc12, hlam, hphi, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      rcases p7880_3 (m.d 0 1) (by simp) with h7889 | h7889
                                      · linarith only [h0, h7889, hlam]
                                      · linarith only [h7464, h7889, hlam]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h0, h7831, h7840, h7841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7464, h7835, h7840, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7827, hlam, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      rcases p7880_3 (m.d 0 1) (by simp) with h7896 | h7896
                                      · linarith only [h6421, h7896, hlam]
                                      · linarith only [h7464, h7896, hlam]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h0, h7827, h7831, h7840, h7841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7464, hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7828, hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7830, hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7832, hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7464, h7835, h7840, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7829, hlam, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7831, hlam, p7880_0]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [h7464, h7465, h7835, h7838, h7840, hc34, hc45, hlam, hphi, p7880_1]
                                    · have p7880_0 := h7880c.1
                                      have p7880_1 := h7880c.2.1
                                      have p7880_2 := h7880c.2.2.1
                                      have p7880_3 := h7880c.2.2.2
                                      linarith only [hlam, p7880_0]
                            · linarith only [h7464, h7465, h7837, h7838, h7840, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h6421, h7830, h7837, hlam]
                      · linarith only [h0, h7829, h7836, hlam]
                    · linarith only [h0, h7828, h7835, hlam]
                  · linarith only [h0, h7827, h7834, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7915 | h7915
                · linarith only [h6421, h7464, h7831, h7915, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7917 | h7917
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7918 | h7918
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7919 | h7919
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7920 | h7920
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7921 | h7921
                          · linarith only [h6421, h7464, h7915, h7921, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7923 | h7923
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7924 | h7924
                              · linarith only [h0, h6421, h7827, h7831, h7924, hc01, hc12, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7926 | h7926
                                · linarith only [h7464, h7465, h7918, h7921, h7926, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7928 | h7928
                                  · linarith only [h7464, h7465, h7918, h7921, h7923, h7928, hlam]
                                  · rcases h0bigk with h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c | h7930c
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h0, hlam, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h6421, hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h6421, h7464, h7918, h7923, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7465, hlam, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h0, h6421, h7464, h7918, h7923, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      rcases p7930_3 (m.d 0 1) (by simp) with h7939 | h7939
                                      · linarith only [h0, h7939, hlam]
                                      · linarith only [h7464, h7939, hlam]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h0, h6421, h7464, h7831, h7918, h7923, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7464, h7918, h7923, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7827, hlam, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7464, h7831, h7918, h7923, h7928, hc34, hc45, hlam, hphi, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7831, hlam, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7464, hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7828, hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7830, hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7915, hlam, p7930_0]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h0, h7464, h7829, h7918, h7923, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7829, hlam, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7831, h7928, hc03, hc45, hlam, hphi, ht34, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [h7464, h7831, h7918, h7923, h7928, hc34, hc45, hlam, hphi, p7930_1]
                                    · have p7930_0 := h7930c.1
                                      have p7930_1 := h7930c.2.1
                                      have p7930_2 := h7930c.2.2.1
                                      have p7930_3 := h7930c.2.2.2
                                      linarith only [hlam, p7930_0]
                            · linarith only [h7830, h7831, h7923, hc23, hc35, hlam, hphi]
                        · linarith only [h7830, h7831, h7920, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h7829, h7919, hlam]
                    · linarith only [h0, h7828, h7918, hlam]
                  · linarith only [h0, h7827, h7917, hlam]
            · linarith only [h6421, h7464, h7830, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7964 | h7964
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7965 | h7965
              · linarith only [h7827, h7829, h7965, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7967 | h7967
                · linarith only [h0, h7464, h7829, h7967, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7969 | h7969
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7970 | h7970
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7971 | h7971
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7972 | h7972
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7973 | h7973
                          · linarith only [h6421, h7464, h7827, h7829, h7967, h7971, h7973, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7975 | h7975
                            · linarith only [h7827, h7829, h7971, h7975, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h7827, h7829, h7964, h7971, h7975, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h6421, h7464, h7964, h7972, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7979 | h7979
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7980 | h7980
                          · linarith only [h0, h7464, h7971, h7980, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7982 | h7982
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7983 | h7983
                              · linarith only [h0, h7827, h7965, h7971, h7983, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7985 | h7985
                                · linarith only [h0, h7464, h7970, h7971, h7980, h7983, h7985, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h7464, h7970, h7971, h7982, h7985, hc34, hc45, hlam, hphi]
                            · linarith only [h7964, h7965, h7982, hc23, hc35, hlam, hphi]
                        · linarith only [h6421, h7964, h7965, h7979, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h7464, h7828, h7970, hlam]
                  · linarith only [h0, h7464, h7827, h7969, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h6421, h7464, h7964, hlam]
        · linarith only [h0, h7464, h7828, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7994 | h7994
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7995 | h7995
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7996 | h7996
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7997 | h7997
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7998 | h7998
                · linarith only [h7464, h7465, h7998, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8000 | h8000
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8001 | h8001
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8002 | h8002
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8003 | h8003
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8004 | h8004
                          · linarith only [h7464, h7465, h7827, h7995, h7998, h8000, h8004, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8006 | h8006
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8007 | h8007
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8008 | h8008
                                · linarith only [h7464, h7465, h7827, h7995, h8000, h8001, h8004, h8008, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8010 | h8010
                                  · linarith only [h7464, h7465, h8001, h8004, h8006, h8010, hlam]
                                  · rcases h0bigk with h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c | h8012c
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h0, hlam, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h6421, hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7465, h7827, h7995, h8000, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7465, hlam, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7827, h8000, hc01, hc12, hlam, hphi, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7827, hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7464, h7827, h8000, h8001, h8006, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7827, h8000, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7464, h8001, h8006, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7827, h8000, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7464, h7827, h8000, h8001, h8006, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7464, h7465, h7827, h8000, h8001, h8006, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7464, hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7994, hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7996, hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7998, hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7464, h7995, h8001, h8006, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7995, hlam, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7997, hlam, p8012_0]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [h7464, h7827, h7995, h8000, h8001, h8006, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8012_1]
                                    · have p8012_0 := h8012c.1
                                      have p8012_1 := h8012c.2.1
                                      have p8012_2 := h8012c.2.2.1
                                      have p8012_3 := h8012c.2.2.2
                                      linarith only [hlam, p8012_0]
                              · linarith only [h7827, h7997, h8007, hlam]
                            · linarith only [h7827, h7996, h8006, hlam]
                        · linarith only [h6421, h7464, h7996, h8003, hlam]
                      · linarith only [h7827, h7995, h8002, hc12, hc23, hlam, hphi]
                    · linarith only [h7827, h8000, h8001, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8043 | h8043
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8044 | h8044
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8045 | h8045
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8046 | h8046
                          · linarith only [h7464, h7465, h8000, h8044, h8046, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8048 | h8048
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8049 | h8049
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8050 | h8050
                                · linarith only [h7464, h7465, h8043, h8046, h8050, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8052 | h8052
                                  · linarith only [h7464, h7465, h8043, h8046, h8048, h8052, hlam]
                                  · rcases h0bigk with h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c | h8054c
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h0, hlam, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h6421, hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7465, h8044, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7465, hlam, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7464, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7827, hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7464, h7827, h8043, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7464, h7465, h7827, h8043, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h6421, h7464, h8000, h8043, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h6421, h8000, hc02, hc23, hlam, hphi, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      rcases p8054_3 (m.d 0 1) (by simp) with h8068 | h8068
                                      · linarith only [h6421, h8068, hlam]
                                      · linarith only [h7464, h8068, hlam]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h6421, h7464, h7465, h8000, h8043, h8048, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7464, hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7994, hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7996, hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7998, hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7464, h7995, h8043, h8048, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7995, hlam, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7997, hlam, p8054_0]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [h7464, h7465, h8043, h8046, h8048, hc34, hc45, hlam, hphi, p8054_1]
                                    · have p8054_0 := h8054c.1
                                      have p8054_1 := h8054c.2.1
                                      have p8054_2 := h8054c.2.2.1
                                      have p8054_3 := h8054c.2.2.2
                                      linarith only [hlam, p8054_0]
                              · linarith only [h0, h7464, h8000, h8043, h8048, h8049, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h7464, h7465, h8000, h8043, h8044, h8048, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h6421, h7996, h8045, hlam]
                      · linarith only [h0, h7995, h8044, hlam]
                    · linarith only [h0, h7994, h8043, hlam]
              · linarith only [h7827, h7995, h7997, hlam]
            · linarith only [h0, h7464, h7827, h7996, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h8089 | h8089
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8090 | h8090
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8091 | h8091
                · linarith only [h0, h7464, h7995, h8091, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8093 | h8093
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8094 | h8094
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8095 | h8095
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8096 | h8096
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8097 | h8097
                          · linarith only [h0, h7464, h7827, h8091, h8093, h8097, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8099 | h8099
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8100 | h8100
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8101 | h8101
                                · linarith only [h0, h7464, h7995, h8094, h8095, h8097, h8101, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8103 | h8103
                                  · linarith only [h0, h7464, h7995, h8094, h8095, h8097, h8099, h8103, hlam]
                                  · rcases h0bigk with h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h0, hlam, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h6421, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h0, h7995, h8093, h8100, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7465, hlam, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7995, h8093, h8100, hc01, hc12, hlam, hphi, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7827, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7464, h7995, h8093, h8094, h8099, h8100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7995, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7464, h8094, h8099, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7827, h8093, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7464, h7827, h8093, h8094, h8099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h0, h7464, h7827, h7995, h8093, h8094, h8099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7464, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7994, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h8089, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h8091, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7464, h8094, h8099, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h0, h7464, h7995, h8093, h8094, h8099, h8100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h8090, hlam, p8105_0]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [h7464, h7995, h8093, h8094, h8099, h8100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8105_1]
                                    · have p8105_0 := h8105c.1
                                      have p8105_1 := h8105c.2.1
                                      have p8105_2 := h8105c.2.2.1
                                      have p8105_3 := h8105c.2.2.2
                                      linarith only [hlam, p8105_0]
                              · linarith only [h7827, h8090, h8100, hlam]
                            · linarith only [h0, h7464, h7827, h8089, h8094, h8099, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h6421, h7464, h8089, h8096, hlam]
                      · linarith only [h0, h7464, h7827, h8093, h8094, h8095, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h7464, h7827, h8093, h8094, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8136 | h8136
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8137 | h8137
                      · linarith only [h0, h7464, h7995, h8093, h8136, h8137, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8139 | h8139
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8140 | h8140
                          · linarith only [h0, h7464, h8091, h8093, h8140, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8142 | h8142
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8143 | h8143
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8144 | h8144
                                · linarith only [h0, h7464, h8136, h8137, h8140, h8143, h8144, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h7464, h8136, h8137, h8142, h8144, hc34, hc45, hlam, hphi]
                              · linarith only [h6421, h8090, h8093, h8143, hlam]
                            · linarith only [h0, h7464, h8093, h8136, h8142, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h7464, h8089, h8093, h8139, hlam]
                    · linarith only [h0, h7464, h7994, h8136, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8151 | h8151
                · linarith only [h7464, h7465, h8151, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8153 | h8153
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8154 | h8154
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8155 | h8155
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8156 | h8156
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8157 | h8157
                          · linarith only [h0, h7464, h7827, h8151, h8153, h8157, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8159 | h8159
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8160 | h8160
                              · linarith only [h0, h7827, h8090, h8153, h8160, hc01, hc12, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8162 | h8162
                                · linarith only [h7464, h7465, h8154, h8157, h8162, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8164 | h8164
                                  · linarith only [h0, h7464, h7827, h8154, h8155, h8157, h8159, h8160, h8164, hlam]
                                  · linarith only [h0, h7464, h7827, h8160, h8164, hc14, hc45, hlam, hphi]
                            · linarith only [h0, h7464, h7827, h8089, h8154, h8159, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h6421, h7464, h8089, h8156, hlam]
                      · linarith only [h0, h7464, h7827, h8153, h8154, h8155, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h7464, h7827, h8153, h8154, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8171 | h8171
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8172 | h8172
                      · linarith only [h0, h7464, h7995, h8153, h8171, h8172, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8174 | h8174
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8175 | h8175
                          · linarith only [h0, h7464, h8153, h8175, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8177 | h8177
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8178 | h8178
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8179 | h8179
                                · linarith only [h0, h7464, h7827, h8090, h8171, h8175, h8178, h8179, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h7464, h8171, h8172, h8177, h8179, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h7464, h8153, h8171, h8177, h8178, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h7464, h8153, h8171, h8177, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h7464, h8089, h8153, h8171, h8174, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7994, h8171, hlam]
            · linarith only [h6421, h7464, h8089, hlam]
        · linarith only [h0, h7464, h7994, hlam]
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9 m hb0 hb2 hb4 h0 h6421 h7464

end R2N4
