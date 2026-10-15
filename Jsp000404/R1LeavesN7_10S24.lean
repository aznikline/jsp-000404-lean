import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6877 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6878 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6879 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h7415 | h7415
  · rcases m.htr 1 2 4 (by decide) (by decide) with h7416 | h7416
    · rcases m.htr 1 2 5 (by decide) (by decide) with h7417 | h7417
      · rcases m.htr 1 3 4 (by decide) (by decide) with h7418 | h7418
        · rcases m.htr 1 4 5 (by decide) (by decide) with h7419 | h7419
          · linarith only [h0, h6874, h6879, h7419, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7421 | h7421
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7422 | h7422
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7423 | h7423
                · linarith only [h6874, h6879, h7416, h7423, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7425 | h7425
                  · linarith only [h6878, h6879, h7425, hlam]
                  · rcases h2bigk with h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c | h7427c
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h0, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7430 | h7430
                      · rcases p7427_3 (m.d 1 2) (by simp) with h7431 | h7431
                        · rcases p7427_3 (m.d 2 3) (by simp) with h7432 | h7432
                          · linarith only [h7432, hlam, p7427_0]
                          · rcases p7427_3 (m.d 2 4) (by simp) with h7434 | h7434
                            · linarith only [h6876, h7434, hlam]
                            · rcases p7427_3 (m.d 2 5) (by simp) with h7436 | h7436
                              · linarith only [h6877, h7436, hlam]
                              · rcases h4bigk with h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c | h7438c
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h0, h6874, h7416, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h6879, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h6874, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h7419, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h6876, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h7416, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h0, h6876, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h7423, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h6878, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h7418, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h7421, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h7425, hlam, p7438_0]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [h7421, hc34, hc45, hlam, hphi, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p7438_1]
                                · have p7438_0 := h7438c.1
                                  have p7438_1 := h7438c.2.1
                                  have p7438_2 := h7438c.2.2.1
                                  have p7438_3 := h7438c.2.2.2
                                  linarith only [hlam, p7438_0]
                        · linarith only [h7415, h7431, hlam]
                      · linarith only [h7430, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7466 | h7466
                      · rcases p7427_3 (m.d 1 2) (by simp) with h7467 | h7467
                        · rcases p7427_3 (m.d 2 3) (by simp) with h7468 | h7468
                          · linarith only [h6875, h7468, hlam]
                          · linarith only [h7421, h7468, hlam]
                        · linarith only [h7416, h7467, hlam]
                      · linarith only [h7466, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7473 | h7473
                      · rcases p7427_3 (m.d 1 2) (by simp) with h7474 | h7474
                        · rcases p7427_3 (m.d 2 3) (by simp) with h7475 | h7475
                          · linarith only [h6875, h7475, hlam]
                          · linarith only [h7422, h7475, hlam]
                        · linarith only [h7417, h7474, hlam]
                      · linarith only [h7473, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h6875, h7422, h7425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7427_1]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7482 | h7482
                      · linarith only [h0, h7482, hlam]
                      · linarith only [h6875, h7482, hlam]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7485 | h7485
                      · linarith only [h0, h7485, hlam]
                      · linarith only [h6876, h7485, hlam]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7488 | h7488
                      · linarith only [h0, h7488, hlam]
                      · linarith only [h6877, h7488, hlam]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h6875, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h7415, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7494 | h7494
                      · rcases p7427_3 (m.d 1 2) (by simp) with h7495 | h7495
                        · rcases p7427_3 (m.d 2 3) (by simp) with h7496 | h7496
                          · rcases p7427_3 (m.d 2 4) (by simp) with h7497 | h7497
                            · linarith only [h7421, h7497, hlam]
                            · rcases p7427_3 (m.d 2 5) (by simp) with h7499 | h7499
                              · linarith only [h7422, h7499, hlam]
                              · linarith only [h7423, h7499, hlam]
                          · linarith only [h7421, h7496, hlam]
                        · linarith only [h7416, h7495, hlam]
                      · linarith only [h6876, h7494, hlam]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7505 | h7505
                      · rcases p7427_3 (m.d 1 2) (by simp) with h7506 | h7506
                        · rcases p7427_3 (m.d 2 3) (by simp) with h7507 | h7507
                          · rcases p7427_3 (m.d 2 4) (by simp) with h7508 | h7508
                            · linarith only [h7421, h7508, hlam]
                            · rcases p7427_3 (m.d 2 5) (by simp) with h7510 | h7510
                              · linarith only [h7422, h7510, hlam]
                              · rcases h4bigk with h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h0, h6874, h7416, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h6879, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h6874, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7419, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h6876, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7416, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h6875, h7423, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7427_1, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7423, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h6878, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7418, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7421, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7425, hlam, p7512_0]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7416, hc24, hc45, hlam, hphi, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [h7421, hc34, hc45, hlam, hphi, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p7512_1]
                                · have p7512_0 := h7512c.1
                                  have p7512_1 := h7512c.2.1
                                  have p7512_2 := h7512c.2.2.1
                                  have p7512_3 := h7512c.2.2.2
                                  linarith only [hlam, p7512_0]
                          · linarith only [h7422, h7507, hlam]
                        · linarith only [h7417, h7506, hlam]
                      · linarith only [h6877, h7505, hlam]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h6876, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h7416, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h7421, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h7423, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h6877, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h7417, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [h7422, hlam, p7427_0]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      rcases p7427_3 (m.d 0 2) (by simp) with h7549 | h7549
                      · rcases p7427_3 (m.d 1 2) (by simp) with h7550 | h7550
                        · rcases p7427_3 (m.d 2 3) (by simp) with h7551 | h7551
                          · rcases p7427_3 (m.d 2 4) (by simp) with h7552 | h7552
                            · linarith only [h7423, h7552, hlam]
                            · rcases p7427_3 (m.d 2 5) (by simp) with h7554 | h7554
                              · rcases h4bigk with h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h0, h6874, h7416, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h6879, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h6874, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h7419, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h6876, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h7416, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h6877, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p7427_1, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h7423, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h6878, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h7418, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h7421, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [h7425, hlam, p7555_0]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hc24, hc45, hlam, hphi, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p7555_1]
                                · have p7555_0 := h7555c.1
                                  have p7555_1 := h7555c.2.1
                                  have p7555_2 := h7555c.2.2.1
                                  have p7555_3 := h7555c.2.2.2
                                  linarith only [hlam, p7555_0]
                              · linarith only [h7423, h7554, hlam]
                          · linarith only [h7421, h7551, hlam]
                        · linarith only [h7416, h7550, hlam]
                      · linarith only [h6876, h7549, hlam]
                    · have p7427_0 := h7427c.1
                      have p7427_1 := h7427c.2.1
                      have p7427_2 := h7427c.2.2.1
                      have p7427_3 := h7427c.2.2.2
                      linarith only [hlam, p7427_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7586 | h7586
                · linarith only [h6874, h6879, h7416, h7586, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7588 | h7588
                  · linarith only [h6878, h6879, h7588, hlam]
                  · rcases h2bigk with h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c | h7590c
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h0, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      rcases p7590_3 (m.d 0 2) (by simp) with h7593 | h7593
                      · rcases p7590_3 (m.d 1 2) (by simp) with h7594 | h7594
                        · rcases p7590_3 (m.d 2 3) (by simp) with h7595 | h7595
                          · linarith only [h7595, hlam, p7590_0]
                          · rcases p7590_3 (m.d 2 4) (by simp) with h7597 | h7597
                            · linarith only [h6876, h7597, hlam]
                            · rcases p7590_3 (m.d 2 5) (by simp) with h7599 | h7599
                              · linarith only [h6877, h7599, hlam]
                              · linarith only [h7422, h7599, hlam]
                        · linarith only [h7415, h7594, hlam]
                      · linarith only [h7593, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      rcases p7590_3 (m.d 0 2) (by simp) with h7604 | h7604
                      · rcases p7590_3 (m.d 1 2) (by simp) with h7605 | h7605
                        · rcases p7590_3 (m.d 2 3) (by simp) with h7606 | h7606
                          · linarith only [h6875, h7606, hlam]
                          · linarith only [h7421, h7606, hlam]
                        · linarith only [h7416, h7605, hlam]
                      · linarith only [h7604, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      rcases p7590_3 (m.d 0 2) (by simp) with h7611 | h7611
                      · rcases p7590_3 (m.d 1 2) (by simp) with h7612 | h7612
                        · rcases p7590_3 (m.d 2 3) (by simp) with h7613 | h7613
                          · linarith only [h6875, h7613, hlam]
                          · rcases p7590_3 (m.d 2 4) (by simp) with h7615 | h7615
                            · linarith only [h6876, h7615, hlam]
                            · rcases p7590_3 (m.d 2 5) (by simp) with h7617 | h7617
                              · linarith only [h7617, hlam, p7590_0]
                              · rcases h4bigk with h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c | h7619c
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h0, h6874, h7416, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h0, h6874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h6879, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h6874, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h0, h6874, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h6874, h6879, hc34, hc45, hlam, hphi, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h7419, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h6876, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h7416, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h6876, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h7586, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h6878, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h7418, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h7421, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h7588, hlam, p7619_0]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [h7421, hc34, hc45, hlam, hphi, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p7619_1]
                                · have p7619_0 := h7619c.1
                                  have p7619_1 := h7619c.2.1
                                  have p7619_2 := h7619c.2.2.1
                                  have p7619_3 := h7619c.2.2.2
                                  linarith only [hlam, p7619_0]
                        · linarith only [h7417, h7612, hlam]
                      · linarith only [h7611, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h6875, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      rcases p7590_3 (m.d 0 2) (by simp) with h7649 | h7649
                      · linarith only [h0, h7649, hlam]
                      · linarith only [h6875, h7649, hlam]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      rcases p7590_3 (m.d 0 2) (by simp) with h7652 | h7652
                      · linarith only [h0, h7652, hlam]
                      · linarith only [h6876, h7652, hlam]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      rcases p7590_3 (m.d 0 2) (by simp) with h7655 | h7655
                      · linarith only [h0, h7655, hlam]
                      · linarith only [h6877, h7655, hlam]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h6875, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h7415, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h7421, h7422, h7588, hc34, hc45, hlam, hphi, p7590_1]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h7422, hlam, p7590_1]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h6876, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h7416, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h7421, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h7586, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h6877, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h7417, hlam, p7590_0]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [h0, h6877, h7421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7590_1]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      rcases p7590_3 (m.d 0 2) (by simp) with h7671 | h7671
                      · rcases p7590_3 (m.d 1 2) (by simp) with h7672 | h7672
                        · rcases p7590_3 (m.d 2 3) (by simp) with h7673 | h7673
                          · linarith only [h7422, h7673, hlam]
                          · linarith only [h7421, h7673, hlam]
                        · linarith only [h7416, h7672, hlam]
                      · linarith only [h6876, h7671, hlam]
                    · have p7590_0 := h7590c.1
                      have p7590_1 := h7590c.2.1
                      have p7590_2 := h7590c.2.2.1
                      have p7590_3 := h7590c.2.2.2
                      linarith only [hlam, p7590_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7679 | h7679
              · linarith only [h0, h6874, h7418, h7421, h7679, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7681 | h7681
                · linarith only [h0, h6874, h6879, h7418, h7421, h7681, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7683 | h7683
                  · linarith only [h6874, h6879, h7418, h7683, hlam]
                  · rcases h2bigk with h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c | h7685c
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h0, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      rcases p7685_3 (m.d 0 2) (by simp) with h7688 | h7688
                      · rcases p7685_3 (m.d 1 2) (by simp) with h7689 | h7689
                        · rcases p7685_3 (m.d 2 3) (by simp) with h7690 | h7690
                          · linarith only [h7690, hlam, p7685_0]
                          · rcases p7685_3 (m.d 2 4) (by simp) with h7692 | h7692
                            · linarith only [h6876, h7692, hlam]
                            · linarith only [h7421, h7692, hlam]
                        · linarith only [h7415, h7689, hlam]
                      · linarith only [h7688, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      rcases p7685_3 (m.d 0 2) (by simp) with h7697 | h7697
                      · rcases p7685_3 (m.d 1 2) (by simp) with h7698 | h7698
                        · rcases p7685_3 (m.d 2 3) (by simp) with h7699 | h7699
                          · linarith only [h6875, h7699, hlam]
                          · rcases p7685_3 (m.d 2 4) (by simp) with h7701 | h7701
                            · linarith only [h7701, hlam, p7685_0]
                            · rcases p7685_3 (m.d 2 5) (by simp) with h7703 | h7703
                              · linarith only [h6877, h7703, hlam]
                              · linarith only [h7681, h7703, hlam]
                        · linarith only [h7416, h7698, hlam]
                      · linarith only [h7697, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      rcases p7685_3 (m.d 0 2) (by simp) with h7708 | h7708
                      · rcases p7685_3 (m.d 1 2) (by simp) with h7709 | h7709
                        · rcases p7685_3 (m.d 2 3) (by simp) with h7710 | h7710
                          · linarith only [h6875, h7710, hlam]
                          · rcases p7685_3 (m.d 2 4) (by simp) with h7712 | h7712
                            · linarith only [h6876, h7712, hlam]
                            · rcases p7685_3 (m.d 2 5) (by simp) with h7714 | h7714
                              · linarith only [h7714, hlam, p7685_0]
                              · rcases h4bigk with h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c | h7716c
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6879, h7418, h7421, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6879, hc24, hc45, hlam, hphi, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6879, h7421, hc23, hc45, hlam, hphi, ht34, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6879, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6874, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6874, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7419, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6876, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7416, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7421, hlam, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7681, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6878, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7418, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h6875, h6878, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7683, hlam, p7716_0]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7421, hc23, hc45, hlam, hphi, ht34, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [h7421, hc23, hc45, hlam, hphi, ht34, p7716_1]
                                · have p7716_0 := h7716c.1
                                  have p7716_1 := h7716c.2.1
                                  have p7716_2 := h7716c.2.2.1
                                  have p7716_3 := h7716c.2.2.2
                                  linarith only [hlam, p7716_0]
                        · linarith only [h7417, h7709, hlam]
                      · linarith only [h7708, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h0, h6874, h7418, h7421, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7685_1]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h0, h6874, h7418, h7421, hlam, p7685_2]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      rcases p7685_3 (m.d 0 2) (by simp) with h7747 | h7747
                      · linarith only [h0, h7747, hlam]
                      · linarith only [h6876, h7747, hlam]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      rcases p7685_3 (m.d 0 2) (by simp) with h7750 | h7750
                      · linarith only [h0, h7750, hlam]
                      · linarith only [h6877, h7750, hlam]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h6875, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h7415, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h7421, hlam, p7685_1]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h7679, hlam, p7685_1]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h6876, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h7416, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h6876, h6879, hc23, hc45, hlam, hphi, ht34, p7685_1]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h7681, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h6877, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [h7417, hlam, p7685_0]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      rcases p7685_3 (m.d 0 2) (by simp) with h7765 | h7765
                      · rcases p7685_3 (m.d 1 2) (by simp) with h7766 | h7766
                        · rcases p7685_3 (m.d 2 3) (by simp) with h7767 | h7767
                          · linarith only [h7679, h7767, hlam]
                          · rcases p7685_3 (m.d 2 4) (by simp) with h7769 | h7769
                            · linarith only [h7681, h7769, hlam]
                            · linarith only [h7421, h7769, hlam]
                        · linarith only [h7415, h7766, hlam]
                      · linarith only [h6875, h7765, hlam]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      rcases p7685_3 (m.d 0 2) (by simp) with h7774 | h7774
                      · rcases p7685_3 (m.d 1 2) (by simp) with h7775 | h7775
                        · rcases p7685_3 (m.d 2 3) (by simp) with h7776 | h7776
                          · linarith only [h7679, h7776, hlam]
                          · rcases p7685_3 (m.d 2 4) (by simp) with h7778 | h7778
                            · linarith only [h7681, h7778, hlam]
                            · rcases p7685_3 (m.d 2 5) (by simp) with h7780 | h7780
                              · rcases h4bigk with h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c | h7781c
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h6879, hc14, hc45, hlam, hphi, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h6879, h7421, hc23, hc45, hlam, hphi, ht34, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h6879, h7421, hc23, hc45, hlam, hphi, ht34, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h6879, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h6874, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h0, h6874, h7421, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7419, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h6876, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7416, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7421, hlam, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7681, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h6878, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7418, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7418, h7421, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7683, hlam, p7781_0]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7421, hc23, hc45, hlam, hphi, ht34, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [h7421, hc23, hc45, hlam, hphi, ht34, p7781_1]
                                · have p7781_0 := h7781c.1
                                  have p7781_1 := h7781c.2.1
                                  have p7781_2 := h7781c.2.2.1
                                  have p7781_3 := h7781c.2.2.2
                                  linarith only [hlam, p7781_0]
                              · linarith only [h7681, h7780, hlam]
                        · linarith only [h7416, h7775, hlam]
                      · linarith only [h6876, h7774, hlam]
                    · have p7685_0 := h7685c.1
                      have p7685_1 := h7685c.2.1
                      have p7685_2 := h7685c.2.2.1
                      have p7685_3 := h7685c.2.2.2
                      linarith only [hlam, p7685_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h7811 | h7811
          · linarith only [h0, h6874, h6879, h7811, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7813 | h7813
            · linarith only [h7415, h7418, h7813, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7815 | h7815
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7816 | h7816
                · linarith only [h6878, h6879, h7415, h7418, h7815, h7816, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h7813, h7815, h7816, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7819 | h7819
                · linarith only [h0, h6876, h6878, h6879, h7415, h7418, h7819, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7821 | h7821
                  · linarith only [h6878, h6879, h7821, hlam]
                  · rcases h2bigk with h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c | h7823c
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h0, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7826 | h7826
                      · rcases p7823_3 (m.d 1 2) (by simp) with h7827 | h7827
                        · rcases p7823_3 (m.d 2 3) (by simp) with h7828 | h7828
                          · linarith only [h7828, hlam, p7823_0]
                          · rcases p7823_3 (m.d 2 4) (by simp) with h7830 | h7830
                            · linarith only [h6876, h7830, hlam]
                            · linarith only [h7813, h7830, hlam]
                        · linarith only [h7415, h7827, hlam]
                      · linarith only [h7826, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7835 | h7835
                      · rcases p7823_3 (m.d 1 2) (by simp) with h7836 | h7836
                        · rcases p7823_3 (m.d 2 3) (by simp) with h7837 | h7837
                          · linarith only [h6875, h7837, hlam]
                          · rcases p7823_3 (m.d 2 4) (by simp) with h7839 | h7839
                            · linarith only [h7839, hlam, p7823_0]
                            · rcases p7823_3 (m.d 2 5) (by simp) with h7841 | h7841
                              · linarith only [h6877, h7841, hlam]
                              · linarith only [h7819, h7841, hlam]
                        · linarith only [h7416, h7836, hlam]
                      · linarith only [h7835, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7846 | h7846
                      · rcases p7823_3 (m.d 1 2) (by simp) with h7847 | h7847
                        · rcases p7823_3 (m.d 2 3) (by simp) with h7848 | h7848
                          · linarith only [h6875, h7848, hlam]
                          · rcases p7823_3 (m.d 2 4) (by simp) with h7850 | h7850
                            · linarith only [h6876, h7850, hlam]
                            · rcases p7823_3 (m.d 2 5) (by simp) with h7852 | h7852
                              · linarith only [h7852, hlam, p7823_0]
                              · rcases h4bigk with h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c | h7854c
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6879, hc14, hc45, hlam, hphi, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6879, h7813, hc23, hc45, hlam, hphi, ht34, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6879, h7415, h7418, hc23, hc45, hlam, hphi, ht34, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6879, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6874, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h0, h6874, h7813, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7418, hlam, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7811, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6876, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7416, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7813, hlam, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7819, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6878, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6875, h6878, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h6878, h6879, h7813, hc23, hc45, hlam, hphi, ht34, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7821, hlam, p7854_0]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7416, h7813, hc23, hc45, hlam, hphi, ht34, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7813, hc23, hc45, hlam, hphi, ht34, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [h7415, h7418, hc23, hc45, hlam, hphi, ht34, p7854_1]
                                · have p7854_0 := h7854c.1
                                  have p7854_1 := h7854c.2.1
                                  have p7854_2 := h7854c.2.2.1
                                  have p7854_3 := h7854c.2.2.2
                                  linarith only [hlam, p7854_0]
                        · linarith only [h7417, h7847, hlam]
                      · linarith only [h7846, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h6875, h6878, h7415, h7418, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7823_1]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7884 | h7884
                      · linarith only [h0, h7884, hlam]
                      · linarith only [h6875, h7884, hlam]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7887 | h7887
                      · linarith only [h0, h7887, hlam]
                      · linarith only [h6876, h7887, hlam]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7890 | h7890
                      · linarith only [h0, h7890, hlam]
                      · linarith only [h6877, h7890, hlam]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h6875, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h7415, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h7813, hlam, p7823_1]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h7815, hlam, p7823_1]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h6876, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h7416, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h0, h6874, h7416, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7823_1]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h7819, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h6877, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [h7417, hlam, p7823_0]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7905 | h7905
                      · rcases p7823_3 (m.d 1 2) (by simp) with h7906 | h7906
                        · rcases p7823_3 (m.d 2 3) (by simp) with h7907 | h7907
                          · linarith only [h7815, h7907, hlam]
                          · rcases p7823_3 (m.d 2 4) (by simp) with h7909 | h7909
                            · linarith only [h7819, h7909, hlam]
                            · linarith only [h7813, h7909, hlam]
                        · linarith only [h7415, h7906, hlam]
                      · linarith only [h6875, h7905, hlam]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      rcases p7823_3 (m.d 0 2) (by simp) with h7914 | h7914
                      · rcases p7823_3 (m.d 1 2) (by simp) with h7915 | h7915
                        · rcases p7823_3 (m.d 2 3) (by simp) with h7916 | h7916
                          · linarith only [h7815, h7916, hlam]
                          · rcases p7823_3 (m.d 2 4) (by simp) with h7918 | h7918
                            · linarith only [h7819, h7918, hlam]
                            · rcases p7823_3 (m.d 2 5) (by simp) with h7920 | h7920
                              · rcases h4bigk with h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c | h7921c
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h0, h6874, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h0, h6874, h7813, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h0, h6874, h7418, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h6879, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h6874, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7418, h7813, hc23, hc34, hlam, hphi, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7418, hlam, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7811, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h6876, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7416, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7813, hlam, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7819, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h6878, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h6878, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h6878, h6879, h7813, hc23, hc45, hlam, hphi, ht34, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7821, hlam, p7921_0]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [hc04, hc45, hlam, hphi, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7416, h7813, hc23, hc45, hlam, hphi, ht34, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7813, hc23, hc45, hlam, hphi, ht34, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [h7415, h7418, hc23, hc45, hlam, hphi, ht34, p7921_1]
                                · have p7921_0 := h7921c.1
                                  have p7921_1 := h7921c.2.1
                                  have p7921_2 := h7921c.2.2.1
                                  have p7921_3 := h7921c.2.2.2
                                  linarith only [hlam, p7921_0]
                              · linarith only [h7819, h7920, hlam]
                        · linarith only [h7416, h7915, hlam]
                      · linarith only [h6876, h7914, hlam]
                    · have p7823_0 := h7823c.1
                      have p7823_1 := h7823c.2.1
                      have p7823_2 := h7823c.2.2.1
                      have p7823_3 := h7823c.2.2.2
                      linarith only [hlam, p7823_0]
      · linarith only [h0, h6877, h7417, hlam]
    · linarith only [h0, h6876, h7416, hlam]
  · linarith only [h0, h6875, h7415, hlam]

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6877 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6878 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h6879 | h6879
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x0_x0 m hb2 hb4 hg0 h6874 h6875 h6876 h6877 h6878 h6879
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x0_x1 m hb2 hb4 hg0 h6874 h6875 h6876 h6877 h6878 h6879

end R2N4
