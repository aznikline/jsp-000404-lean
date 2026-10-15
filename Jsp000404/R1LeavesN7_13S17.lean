import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S15
import Jsp000404.R1LeavesN7_13S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11000000 in
set_option maxHeartbeats 11000000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s6_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6923 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6924 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  rcases m.htr 0 2 3 (by decide) (by decide) with h7433 | h7433
  · rcases m.htr 0 2 4 (by decide) (by decide) with h7434 | h7434
    · rcases m.htr 0 2 5 (by decide) (by decide) with h7435 | h7435
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7436 | h7436
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7437 | h7437
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7438 | h7438
            · linarith only [h6923, h6924, h7438, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7440 | h7440
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7441 | h7441
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7442 | h7442
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7443 | h7443
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7444 | h7444
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7445 | h7445
                        · linarith only [h6923, h6924, h7438, h7440, h7444, h7445, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7447 | h7447
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7448 | h7448
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7449 | h7449
                              · linarith only [h6923, h6924, h7441, h7445, h7449, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7451 | h7451
                                · linarith only [h6924, h7433, h7445, h7447, h7451, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h2bigk with h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h0, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h0, h7448, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7453_1]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    rcases p7453_3 (m.d 0 2) (by simp) with h7457 | h7457
                                    · rcases p7453_3 (m.d 1 2) (by simp) with h7458 | h7458
                                      · rcases p7453_3 (m.d 2 3) (by simp) with h7459 | h7459
                                        · linarith only [h7433, h7459, hlam]
                                        · linarith only [h7447, h7459, hlam]
                                      · linarith only [h7441, h7458, hlam]
                                    · linarith only [h7457, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    rcases p7453_3 (m.d 0 2) (by simp) with h7464 | h7464
                                    · rcases p7453_3 (m.d 1 2) (by simp) with h7465 | h7465
                                      · rcases p7453_3 (m.d 2 3) (by simp) with h7466 | h7466
                                        · linarith only [h7433, h7466, hlam]
                                        · linarith only [h7448, h7466, hlam]
                                      · linarith only [h7442, h7465, hlam]
                                    · linarith only [h7464, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h0, h6923, h7441, h7447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7453_1]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7448, h7451, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7453_1]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    rcases p7453_3 (m.d 0 2) (by simp) with h7474 | h7474
                                    · linarith only [h0, h7474, hlam]
                                    · linarith only [h7434, h7474, hlam]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    rcases p7453_3 (m.d 0 2) (by simp) with h7477 | h7477
                                    · linarith only [h0, h7477, hlam]
                                    · linarith only [h7435, h7477, hlam]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7433, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7440, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7433, h7447, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7453_1]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h0, h7433, h7448, h7451, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7453_1]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7434, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7441, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7447, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7449, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7435, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7442, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h7448, hlam, p7453_0]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [h0, h7435, h7447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7453_1]
                                  · have p7453_0 := h7453c.1
                                    have p7453_1 := h7453c.2.1
                                    have p7453_2 := h7453c.2.2.1
                                    have p7453_3 := h7453c.2.2.2
                                    linarith only [hlam, p7453_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7495 | h7495
                              · linarith only [h6923, h6924, h7441, h7445, h7495, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7497 | h7497
                                · linarith only [h6923, h6924, h7441, h7445, h7447, h7497, hlam]
                                · rcases h2bigk with h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c | h7499c
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h0, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h0, h7447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    rcases p7499_3 (m.d 0 2) (by simp) with h7503 | h7503
                                    · rcases p7499_3 (m.d 1 2) (by simp) with h7504 | h7504
                                      · rcases p7499_3 (m.d 2 3) (by simp) with h7505 | h7505
                                        · linarith only [h7433, h7505, hlam]
                                        · linarith only [h7447, h7505, hlam]
                                      · linarith only [h7441, h7504, hlam]
                                    · linarith only [h7503, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h0, h7447, h7448, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h0, h6923, h7441, h7447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    rcases p7499_3 (m.d 0 2) (by simp) with h7514 | h7514
                                    · linarith only [h0, h7514, hlam]
                                    · linarith only [h7434, h7514, hlam]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7447, h7448, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7433, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7440, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7433, h7447, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7448, hlam, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7434, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7441, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7447, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7495, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7435, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7442, hlam, p7499_0]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h0, h7435, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [h7437, h7447, h7448, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7499_1]
                                  · have p7499_0 := h7499c.1
                                    have p7499_1 := h7499c.2.1
                                    have p7499_2 := h7499c.2.2.1
                                    have p7499_3 := h7499c.2.2.2
                                    linarith only [hlam, p7499_0]
                          · linarith only [h6923, h6924, h7443, h7445, h7447, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h5135, h7437, h7444, hlam]
                    · linarith only [h5135, h7436, h7443, hlam]
                  · linarith only [h0, h7435, h7442, hlam]
                · linarith only [h0, h7434, h7441, hlam]
              · linarith only [h0, h7433, h7440, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7539 | h7539
            · linarith only [h5135, h6923, h7437, h7539, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7541 | h7541
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7542 | h7542
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7543 | h7543
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7544 | h7544
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7545 | h7545
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7546 | h7546
                        · linarith only [h5135, h6923, h7437, h7539, h7541, h7545, h7546, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7548 | h7548
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7549 | h7549
                            · linarith only [h5135, h6923, h7433, h7437, h7549, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7551 | h7551
                              · linarith only [h5135, h6923, h7437, h7542, h7545, h7546, h7551, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7553 | h7553
                                · linarith only [h5135, h6923, h7437, h7542, h7545, h7546, h7548, h7553, hlam]
                                · rcases h2bigk with h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c | h7555c
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h0, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h0, h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    rcases p7555_3 (m.d 0 2) (by simp) with h7559 | h7559
                                    · rcases p7555_3 (m.d 1 2) (by simp) with h7560 | h7560
                                      · rcases p7555_3 (m.d 2 3) (by simp) with h7561 | h7561
                                        · linarith only [h7433, h7561, hlam]
                                        · linarith only [h7548, h7561, hlam]
                                      · linarith only [h7542, h7560, hlam]
                                    · linarith only [h7559, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h0, h7548, h7549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h0, h6923, h7542, h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7548, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    rcases p7555_3 (m.d 0 2) (by simp) with h7570 | h7570
                                    · linarith only [h0, h7570, hlam]
                                    · linarith only [h7434, h7570, hlam]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7548, h7549, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7433, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7541, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7435, h7548, h7549, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7549, hlam, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7434, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7542, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7548, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7551, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7435, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7543, hlam, p7555_0]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h7435, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [h6924, h7435, h7546, h7548, hc34, hc45, hlam, hphi, p7555_1]
                                  · have p7555_0 := h7555c.1
                                    have p7555_1 := h7555c.2.1
                                    have p7555_2 := h7555c.2.2.1
                                    have p7555_3 := h7555c.2.2.2
                                    linarith only [hlam, p7555_0]
                          · linarith only [h7436, h7437, h7545, h7548, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7590 | h7590
                        · linarith only [h5135, h6923, h7539, h7545, h7590, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7592 | h7592
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7593 | h7593
                            · linarith only [h5135, h7545, h7593, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7595 | h7595
                              · linarith only [h5135, h6923, h7542, h7545, h7590, h7595, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7597 | h7597
                                · linarith only [h5135, h6923, h7542, h7545, h7590, h7592, h7597, hlam]
                                · linarith only [h5135, h6923, h7542, h7545, h7592, h7597, hc34, hc45, hlam, hphi]
                          · linarith only [h5135, h7436, h7545, h7592, hc23, hc35, hlam, hphi]
                    · linarith only [h5135, h6923, h7436, h7544, hlam]
                  · linarith only [h0, h7435, h7543, hlam]
                · linarith only [h0, h7434, h7542, hlam]
              · linarith only [h0, h7433, h7541, hlam]
        · linarith only [h5135, h6923, h7436, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7606 | h7606
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7607 | h7607
          · linarith only [h7433, h7435, h7607, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7609 | h7609
            · linarith only [h5135, h6923, h7433, h7435, h7609, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7611 | h7611
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7612 | h7612
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7613 | h7613
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7614 | h7614
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7615 | h7615
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7616 | h7616
                        · linarith only [h5135, h6923, h7433, h7435, h7609, h7613, h7616, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7618 | h7618
                          · linarith only [h7433, h7435, h7613, h7618, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h7433, h7435, h7606, h7613, h7618, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7621 | h7621
                        · linarith only [h5135, h6923, h7433, h7435, h7613, h7621, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7623 | h7623
                          · linarith only [h7433, h7435, h7613, h7623, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h7433, h7435, h7606, h7613, h7623, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h5135, h6923, h7606, h7614, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7627 | h7627
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7628 | h7628
                      · linarith only [h5135, h7607, h7611, h7613, h7628, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7630 | h7630
                        · linarith only [h0, h6923, h7613, h7630, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7632 | h7632
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7633 | h7633
                            · linarith only [h0, h7433, h7613, h7628, h7633, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7635 | h7635
                              · linarith only [h0, h6923, h7612, h7613, h7630, h7633, h7635, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h5135, h6923, h7611, h7613, h7635, hc14, hc45, hlam, hphi]
                          · linarith only [h5135, h7606, h7628, h7632, hc23, hc35, hlam, hphi]
                    · linarith only [h5135, h6923, h7606, h7627, hlam]
                · linarith only [h0, h7434, h7612, hlam]
              · linarith only [h0, h7433, h7611, hlam]
        · linarith only [h5135, h6923, h7606, hlam]
    · linarith only [h0, h6923, h7434, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h7644 | h7644
    · rcases m.htr 0 2 5 (by decide) (by decide) with h7645 | h7645
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7646 | h7646
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7647 | h7647
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7648 | h7648
            · linarith only [h6923, h6924, h7648, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7650 | h7650
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7651 | h7651
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7652 | h7652
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7653 | h7653
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7654 | h7654
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7655 | h7655
                        · linarith only [h6923, h6924, h7433, h7645, h7648, h7650, h7655, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7657 | h7657
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7658 | h7658
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7659 | h7659
                              · linarith only [h6923, h6924, h7651, h7655, h7659, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7661 | h7661
                                · linarith only [h6923, h6924, h7651, h7655, h7657, h7661, hlam]
                                · rcases h2bigk with h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c | h7663c
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h0, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7433, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7433, h7650, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7433, h7650, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h6924, h7645, hc01, hc12, hlam, hphi, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h5135, h6923, h7433, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    rcases p7663_3 (m.d 0 2) (by simp) with h7672 | h7672
                                    · linarith only [h0, h7672, hlam]
                                    · linarith only [h7644, h7672, hlam]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    rcases p7663_3 (m.d 0 2) (by simp) with h7675 | h7675
                                    · linarith only [h0, h7675, hlam]
                                    · linarith only [h7645, h7675, hlam]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h6923, h6924, h7645, h7650, h7651, h7657, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7650, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7650, h7657, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7650, h7657, h7659, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7644, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7651, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7657, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7659, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7645, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7652, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7658, hlam, p7663_0]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [h7645, h7657, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7663_1]
                                  · have p7663_0 := h7663c.1
                                    have p7663_1 := h7663c.2.1
                                    have p7663_2 := h7663c.2.2.1
                                    have p7663_3 := h7663c.2.2.2
                                    linarith only [hlam, p7663_0]
                            · linarith only [h7433, h7647, h7658, hlam]
                          · linarith only [h7433, h7646, h7657, hlam]
                      · linarith only [h5135, h7433, h7645, h7647, h7654, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h5135, h7646, h7653, hlam]
                  · linarith only [h7433, h7650, h7652, hc02, hc25, hlam, hphi]
                · linarith only [h6923, h6924, h7433, h7645, h7650, h7651, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7699 | h7699
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7700 | h7700
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7701 | h7701
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7702 | h7702
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7703 | h7703
                        · linarith only [h0, h6923, h7650, h7703, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7705 | h7705
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7706 | h7706
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7707 | h7707
                              · linarith only [h6923, h6924, h7699, h7703, h7707, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7709 | h7709
                                · linarith only [h6923, h6924, h7699, h7703, h7705, h7709, hlam]
                                · rcases h2bigk with h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c | h7711c
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h0, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7433, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h0, h7650, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h0, h7650, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7650, hc02, hc23, hlam, hphi, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7650, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7650, h7705, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7650, h7706, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h6924, h7645, hc01, hc23, hlam, hphi, ht12, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [hc12, hc23, hlam, hphi, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    rcases p7711_3 (m.d 0 2) (by simp) with h7725 | h7725
                                    · linarith only [h7433, h7725, hlam]
                                    · linarith only [h7644, h7725, hlam]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    rcases p7711_3 (m.d 0 2) (by simp) with h7728 | h7728
                                    · linarith only [h7433, h7728, hlam]
                                    · linarith only [h7645, h7728, hlam]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7644, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7699, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7705, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7707, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7645, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7700, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7706, hlam, p7711_0]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [h7645, h7705, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7711_1]
                                  · have p7711_0 := h7711c.1
                                    have p7711_1 := h7711c.2.1
                                    have p7711_2 := h7711c.2.2.1
                                    have p7711_3 := h7711c.2.2.2
                                    linarith only [hlam, p7711_0]
                            · linarith only [h5135, h7433, h7645, h7647, h7706, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h6923, h6924, h7433, h7645, h7646, h7705, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h5135, h6923, h7645, h7647, h7650, h7699, h7702, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h5135, h7646, h7701, hlam]
                  · linarith only [h0, h6923, h7645, h7699, h7700, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h7644, h7699, hlam]
          · linarith only [h7433, h7645, h7647, hlam]
        · linarith only [h0, h6923, h7433, h7646, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7749 | h7749
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7750 | h7750
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7751 | h7751
            · linarith only [h0, h6923, h7645, h7751, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7753 | h7753
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7754 | h7754
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7755 | h7755
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7756 | h7756
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7757 | h7757
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7758 | h7758
                        · linarith only [h0, h6923, h7433, h7751, h7753, h7758, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7760 | h7760
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7761 | h7761
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7762 | h7762
                              · linarith only [h0, h6923, h7645, h7754, h7755, h7758, h7762, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7764 | h7764
                                · linarith only [h0, h6923, h7645, h7754, h7755, h7758, h7760, h7764, hlam]
                                · rcases h2bigk with h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c | h7766c
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h0, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7433, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7645, h7753, h7761, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7645, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h0, h6923, h7433, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    rcases p7766_3 (m.d 0 2) (by simp) with h7775 | h7775
                                    · linarith only [h0, h7775, hlam]
                                    · linarith only [h7644, h7775, hlam]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h0, h6923, h7645, h7754, h7760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h0, h6923, h7753, h7754, h7760, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7753, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7753, h7760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h0, h6923, h7645, h7753, h7754, h7760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7644, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7754, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7760, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7762, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h0, h6923, h7754, h7755, h7760, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7755, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7761, hlam, p7766_0]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [h7753, h7760, h7761, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7766_1]
                                  · have p7766_0 := h7766c.1
                                    have p7766_1 := h7766c.2.1
                                    have p7766_2 := h7766c.2.2.1
                                    have p7766_3 := h7766c.2.2.2
                                    linarith only [hlam, p7766_0]
                            · linarith only [h0, h6923, h7433, h7750, h7754, h7760, h7761, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h6923, h7433, h7749, h7754, h7760, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h5135, h7750, h7757, hlam]
                    · linarith only [h7433, h7749, h7753, h7756, hlam]
                  · linarith only [h0, h6923, h7433, h7753, h7754, h7755, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h7433, h7753, h7754, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7800 | h7800
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7801 | h7801
                  · linarith only [h0, h6923, h7645, h7753, h7800, h7801, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7803 | h7803
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7804 | h7804
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7805 | h7805
                        · linarith only [h0, h6923, h7751, h7753, h7805, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7807 | h7807
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7808 | h7808
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7809 | h7809
                              · linarith only [h0, h6923, h7800, h7801, h7805, h7808, h7809, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h6923, h7800, h7801, h7807, h7809, hc34, hc45, hlam, hphi]
                            · linarith only [h5135, h7750, h7753, h7808, hlam]
                          · linarith only [h0, h6923, h7753, h7800, h7807, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h5135, h7750, h7804, hlam]
                    · linarith only [h5135, h7749, h7803, hlam]
                · linarith only [h0, h6923, h7644, h7800, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7817 | h7817
            · linarith only [h5135, h6923, h7750, h7817, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7819 | h7819
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7820 | h7820
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7821 | h7821
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7822 | h7822
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7823 | h7823
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7824 | h7824
                        · linarith only [h0, h6923, h7433, h7750, h7817, h7819, h7823, h7824, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7826 | h7826
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7827 | h7827
                            · linarith only [h0, h7433, h7750, h7819, h7827, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h6923, h7433, h7820, h7823, h7826, h7827, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h6923, h7433, h7749, h7820, h7826, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7831 | h7831
                        · linarith only [h0, h6923, h7433, h7750, h7817, h7831, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7833 | h7833
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7834 | h7834
                            · linarith only [h5135, h6923, h7820, h7823, h7833, h7834, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7836 | h7836
                              · linarith only [h0, h6923, h7433, h7819, h7820, h7821, h7823, h7831, h7836, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7838 | h7838
                                · linarith only [h0, h6923, h7433, h7819, h7820, h7823, h7831, h7833, h7838, hlam]
                                · linarith only [h0, h6923, h7433, h7819, h7820, h7823, h7833, h7838, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h6923, h7433, h7749, h7820, h7833, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h5135, h6923, h7749, h7822, hlam]
                  · linarith only [h0, h7433, h7819, h7821, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h6923, h7433, h7819, h7820, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7845 | h7845
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7846 | h7846
                  · linarith only [h0, h6923, h7645, h7819, h7845, h7846, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7848 | h7848
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7849 | h7849
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7850 | h7850
                        · linarith only [h0, h6923, h7433, h7750, h7849, h7850, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7852 | h7852
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7853 | h7853
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7854 | h7854
                              · linarith only [h0, h6923, h7433, h7750, h7845, h7849, h7850, h7854, hlam]
                              · linarith only [h0, h6923, h7846, h7854, hc14, hc45, hlam, hphi]
                            · linarith only [h7819, h7849, h7853, hlam]
                          · linarith only [h0, h7433, h7750, h7819, h7849, h7852, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7859 | h7859
                        · linarith only [h0, h6923, h7819, h7859, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7861 | h7861
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7862 | h7862
                            · linarith only [h0, h7819, h7849, h7862, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h6923, h7819, h7845, h7861, h7862, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h6923, h7819, h7845, h7861, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h6923, h7749, h7819, h7845, h7848, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h7644, h7845, hlam]
        · linarith only [h5135, h6923, h7749, hlam]
    · linarith only [h0, h6923, h7644, hlam]

set_option maxHeartbeats 11000000 in
set_option maxHeartbeats 11000000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s6_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6923 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  rcases m.htr 0 1 5 (by decide) (by decide) with h6924 | h6924
  · exact r1l7_22_13_15_H_I_L_I_L_I_s6_x0_x0 m hb2 hb3 hb5 hg0 hg5135 h6923 h6924
  · exact r1l7_22_13_15_H_I_L_I_L_I_s6_x0_x1 m hb2 hb3 hb5 hg0 hg5135 h6923 h6924

set_option maxHeartbeats 11000000 in
set_option maxHeartbeats 11000000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s6_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  exact r1l7_22_13_15_H_I_L_I_L_I_s7 m hb2 hb3 hb5 h0 h5135 h6923

set_option maxHeartbeats 11000000 in
set_option maxHeartbeats 11000000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s6 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  rcases m.htr 0 1 4 (by decide) (by decide) with h6923 | h6923
  · exact r1l7_22_13_15_H_I_L_I_L_I_s6_x0 m hb2 hb3 hb5 hg0 hg5135 h6923
  · exact r1l7_22_13_15_H_I_L_I_L_I_s6_x1 m hb2 hb3 hb5 hg0 hg5135 h6923

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5139 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5140 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5141 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h5142 | h5142
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5143 | h5143
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5144 | h5144
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5145 | h5145
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5146 | h5146
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5147 | h5147
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5148 | h5148
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5149 | h5149
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5150 | h5150
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5151 | h5151
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5152 | h5152
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5153 | h5153
                        · linarith only [h0, h5135, h5144, h5150, h5153, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h5135, h5147, h5149, h5153, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h5135, h5147, h5149, h5152, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h5135, h5148, h5151, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h5135, h5147, h5150, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5159 | h5159
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5160 | h5160
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5161 | h5161
                      · linarith only [h5145, h5149, h5161, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5163 | h5163
                        · linarith only [h5138, h5145, h5149, h5159, h5163, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h2bigk with h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c | h5165c
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h0, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5160, hc02, hc35, hlam, hphi, ht0b, ht5b, p5165_1]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            rcases p5165_3 (m.d 0 2) (by simp) with h5169 | h5169
                            · rcases p5165_3 (m.d 1 2) (by simp) with h5170 | h5170
                              · rcases p5165_3 (m.d 2 3) (by simp) with h5171 | h5171
                                · linarith only [h5138, h5171, hlam]
                                · linarith only [h5159, h5171, hlam]
                              · linarith only [h5145, h5170, hlam]
                            · linarith only [h5169, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            rcases p5165_3 (m.d 0 2) (by simp) with h5176 | h5176
                            · rcases p5165_3 (m.d 1 2) (by simp) with h5177 | h5177
                              · rcases p5165_3 (m.d 2 3) (by simp) with h5178 | h5178
                                · linarith only [h5138, h5178, hlam]
                                · linarith only [h5160, h5178, hlam]
                              · linarith only [h5146, h5177, hlam]
                            · linarith only [h5176, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5165_1]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5160, h5163, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5165_1]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            rcases p5165_3 (m.d 0 2) (by simp) with h5186 | h5186
                            · linarith only [h0, h5186, hlam]
                            · linarith only [h5139, h5186, hlam]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            rcases p5165_3 (m.d 0 2) (by simp) with h5189 | h5189
                            · linarith only [h0, h5189, hlam]
                            · linarith only [h5140, h5189, hlam]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5138, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5144, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5138, h5159, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5165_1]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5135, h5144, h5160, h5163, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5165_1]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5139, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5145, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5159, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5161, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5140, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5146, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h5160, hlam, p5165_0]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [h0, h5140, h5159, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5165_1]
                          · have p5165_0 := h5165c.1
                            have p5165_1 := h5165c.2.1
                            have p5165_2 := h5165c.2.2.1
                            have p5165_3 := h5165c.2.2.2
                            linarith only [hlam, p5165_0]
                    · linarith only [h0, h5135, h5148, h5160, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h5135, h5147, h5159, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h5135, h5142, h5147, h5148, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5210 | h5210
              · linarith only [h0, h5135, h5141, h5147, h5210, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5212 | h5212
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5213 | h5213
                  · linarith only [h5144, h5147, h5213, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5215 | h5215
                    · linarith only [h5144, h5210, h5215, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5217 | h5217
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5218 | h5218
                        · rcases h2bigk with h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c | h5219c
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h0, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            rcases p5219_3 (m.d 0 2) (by simp) with h5222 | h5222
                            · rcases p5219_3 (m.d 1 2) (by simp) with h5223 | h5223
                              · rcases p5219_3 (m.d 2 3) (by simp) with h5224 | h5224
                                · linarith only [h5224, hlam, p5219_0]
                                · rcases p5219_3 (m.d 2 4) (by simp) with h5226 | h5226
                                  · linarith only [h5139, h5226, hlam]
                                  · linarith only [h5213, h5226, hlam]
                              · linarith only [h5144, h5223, hlam]
                            · linarith only [h5222, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h0, h5217, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            rcases p5219_3 (m.d 0 2) (by simp) with h5232 | h5232
                            · rcases p5219_3 (m.d 1 2) (by simp) with h5233 | h5233
                              · rcases p5219_3 (m.d 2 3) (by simp) with h5234 | h5234
                                · linarith only [h5138, h5234, hlam]
                                · rcases p5219_3 (m.d 2 4) (by simp) with h5236 | h5236
                                  · linarith only [h5139, h5236, hlam]
                                  · linarith only [h5217, h5236, hlam]
                              · linarith only [h5146, h5233, hlam]
                            · linarith only [h5232, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            rcases p5219_3 (m.d 0 2) (by simp) with h5243 | h5243
                            · linarith only [h0, h5243, hlam]
                            · linarith only [h5138, h5243, hlam]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5217, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            rcases p5219_3 (m.d 0 2) (by simp) with h5247 | h5247
                            · linarith only [h0, h5247, hlam]
                            · linarith only [h5140, h5247, hlam]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5138, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5144, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5213, hlam, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5215, hlam, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5139, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5145, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5139, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5135, h5141, h5145, h5147, h5215, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5140, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5146, hlam, p5219_0]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h0, h5140, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [h5217, hlam, p5219_1]
                          · have p5219_0 := h5219c.1
                            have p5219_1 := h5219c.2.1
                            have p5219_2 := h5219c.2.2.1
                            have p5219_3 := h5219c.2.2.2
                            linarith only [hlam, p5219_0]
                        · linarith only [h0, h5135, h5141, h5143, h5144, h5147, h5218, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h5136, h5212, h5217, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5267 | h5267
                  · linarith only [h5144, h5147, h5267, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5269 | h5269
                    · linarith only [h0, h5135, h5141, h5143, h5144, h5147, h5210, h5212, h5269, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5271 | h5271
                      · linarith only [h5145, h5212, h5271, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5273 | h5273
                        · linarith only [h0, h5135, h5141, h5147, h5212, h5273, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h5135, h5141, h5143, h5144, h5147, h5273, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h5140, h5146, hlam]
        · linarith only [h0, h5139, h5145, hlam]
      · linarith only [h0, h5138, h5144, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5279 | h5279
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5280 | h5280
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5281 | h5281
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5282 | h5282
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5283 | h5283
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5284 | h5284
                · linarith only [h0, h5135, h5143, h5282, h5284, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5286 | h5286
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5287 | h5287
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5288 | h5288
                      · linarith only [h5136, h5143, h5280, h5288, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5290 | h5290
                        · linarith only [h0, h5135, h5136, h5141, h5143, h5280, h5290, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h2bigk with h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h0, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h0, h5286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5292_1]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            rcases p5292_3 (m.d 0 2) (by simp) with h5296 | h5296
                            · rcases p5292_3 (m.d 1 2) (by simp) with h5297 | h5297
                              · rcases p5292_3 (m.d 2 3) (by simp) with h5298 | h5298
                                · linarith only [h5138, h5298, hlam]
                                · linarith only [h5286, h5298, hlam]
                              · linarith only [h5280, h5297, hlam]
                            · linarith only [h5296, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            rcases p5292_3 (m.d 0 2) (by simp) with h5303 | h5303
                            · rcases p5292_3 (m.d 1 2) (by simp) with h5304 | h5304
                              · rcases p5292_3 (m.d 2 3) (by simp) with h5305 | h5305
                                · linarith only [h5138, h5305, hlam]
                                · linarith only [h5287, h5305, hlam]
                              · linarith only [h5281, h5304, hlam]
                            · linarith only [h5303, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5292_1]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5287, h5290, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5292_1]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            rcases p5292_3 (m.d 0 2) (by simp) with h5313 | h5313
                            · linarith only [h0, h5313, hlam]
                            · linarith only [h5139, h5313, hlam]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            rcases p5292_3 (m.d 0 2) (by simp) with h5316 | h5316
                            · linarith only [h0, h5316, hlam]
                            · linarith only [h5140, h5316, hlam]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5138, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5279, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5135, h5279, h5286, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5292_1]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h0, h5135, h5279, h5286, h5288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5292_1]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5139, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5280, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5286, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5288, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5140, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5281, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h5287, hlam, p5292_0]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [h0, h5140, h5286, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5292_1]
                          · have p5292_0 := h5292c.1
                            have p5292_1 := h5292c.2.1
                            have p5292_2 := h5292c.2.2.1
                            have p5292_3 := h5292c.2.2.2
                            linarith only [hlam, p5292_0]
                    · linarith only [h0, h5135, h5283, h5287, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h5135, h5282, h5286, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h5135, h5142, h5282, h5283, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5337 | h5337
              · linarith only [h0, h5135, h5141, h5282, h5337, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5339 | h5339
                · linarith only [h0, h5136, h5143, h5339, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5341 | h5341
                  · linarith only [h5279, h5282, h5341, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5343 | h5343
                    · linarith only [h0, h5135, h5141, h5279, h5281, h5282, h5337, h5343, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5345 | h5345
                      · linarith only [h5139, h5141, h5143, h5279, h5282, h5345, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5347 | h5347
                        · linarith only [h5141, h5143, h5347, hlam]
                        · rcases h2bigk with h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c | h5349c
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h0, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            rcases p5349_3 (m.d 0 2) (by simp) with h5352 | h5352
                            · rcases p5349_3 (m.d 1 2) (by simp) with h5353 | h5353
                              · rcases p5349_3 (m.d 2 3) (by simp) with h5354 | h5354
                                · linarith only [h5354, hlam, p5349_0]
                                · rcases p5349_3 (m.d 2 4) (by simp) with h5356 | h5356
                                  · linarith only [h5139, h5356, hlam]
                                  · linarith only [h5341, h5356, hlam]
                              · linarith only [h5279, h5353, hlam]
                            · linarith only [h5352, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            rcases p5349_3 (m.d 0 2) (by simp) with h5361 | h5361
                            · rcases p5349_3 (m.d 1 2) (by simp) with h5362 | h5362
                              · rcases p5349_3 (m.d 2 3) (by simp) with h5363 | h5363
                                · linarith only [h5138, h5363, hlam]
                                · rcases p5349_3 (m.d 2 4) (by simp) with h5365 | h5365
                                  · linarith only [h5365, hlam, p5349_0]
                                  · rcases p5349_3 (m.d 2 5) (by simp) with h5367 | h5367
                                    · linarith only [h5140, h5367, hlam]
                                    · linarith only [h5345, h5367, hlam]
                              · linarith only [h5280, h5362, hlam]
                            · linarith only [h5361, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            rcases p5349_3 (m.d 0 2) (by simp) with h5372 | h5372
                            · rcases p5349_3 (m.d 1 2) (by simp) with h5373 | h5373
                              · rcases p5349_3 (m.d 2 3) (by simp) with h5374 | h5374
                                · linarith only [h5138, h5374, hlam]
                                · rcases p5349_3 (m.d 2 4) (by simp) with h5376 | h5376
                                  · linarith only [h5139, h5376, hlam]
                                  · rcases p5349_3 (m.d 2 5) (by simp) with h5378 | h5378
                                    · linarith only [h5378, hlam, p5349_0]
                                    · rcases h3bigk with h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c | h5380c
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        rcases p5380_3 (m.d 0 3) (by simp) with h5382 | h5382
                                        · rcases p5380_3 (m.d 1 3) (by simp) with h5383 | h5383
                                          · linarith only [h5135, h5383, hlam]
                                          · rcases p5380_3 (m.d 2 3) (by simp) with h5385 | h5385
                                            · linarith only [h5138, h5385, hlam]
                                            · rcases p5380_3 (m.d 3 4) (by simp) with h5387 | h5387
                                              · linarith only [h5141, h5387, hlam]
                                              · linarith only [h5282, h5387, hlam]
                                        · linarith only [h5135, h5382, hlam]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        rcases p5380_3 (m.d 0 3) (by simp) with h5391 | h5391
                                        · rcases p5380_3 (m.d 1 3) (by simp) with h5392 | h5392
                                          · linarith only [h5135, h5392, hlam]
                                          · linarith only [h5279, h5392, hlam]
                                        · linarith only [h5138, h5391, hlam]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h0, h5135, h5279, h5282, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h0, h5135, h5279, h5282, h5347, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5135, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5282, hc23, hc34, hlam, hphi, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5282, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5337, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5138, hlam, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5279, hlam, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5341, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5343, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5141, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h0, h5135, h5141, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h0, h5135, h5141, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5347, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h5142, hlam, p5380_0]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h0, h5135, h5142, h5279, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h0, h5135, h5142, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [h0, h5135, h5142, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5380_1]
                                      · have p5380_0 := h5380c.1
                                        have p5380_1 := h5380c.2.1
                                        have p5380_2 := h5380c.2.2.1
                                        have p5380_3 := h5380c.2.2.2
                                        linarith only [hlam, p5380_0]
                              · linarith only [h5281, h5373, hlam]
                            · linarith only [h5372, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5349_1]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            rcases p5349_3 (m.d 0 2) (by simp) with h5422 | h5422
                            · linarith only [h0, h5422, hlam]
                            · linarith only [h5138, h5422, hlam]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            rcases p5349_3 (m.d 0 2) (by simp) with h5425 | h5425
                            · linarith only [h0, h5425, hlam]
                            · linarith only [h5139, h5425, hlam]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            rcases p5349_3 (m.d 0 2) (by simp) with h5428 | h5428
                            · linarith only [h0, h5428, hlam]
                            · linarith only [h5140, h5428, hlam]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5138, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5279, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5341, hlam, p5349_1]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5343, hlam, p5349_1]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5139, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5280, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5136, h5280, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5349_1]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5345, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5140, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5281, hlam, p5349_0]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h5142, h5281, h5337, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5349_1]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [h0, h5135, h5142, h5281, h5337, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5349_1]
                          · have p5349_0 := h5349c.1
                            have p5349_1 := h5349c.2.1
                            have p5349_2 := h5349c.2.2.1
                            have p5349_3 := h5349c.2.2.2
                            linarith only [hlam, p5349_0]
          · linarith only [h0, h5140, h5281, hlam]
        · linarith only [h0, h5139, h5280, hlam]
      · linarith only [h0, h5138, h5279, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5449 | h5449
    · linarith only [h5141, h5142, h5449, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5451 | h5451
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5452 | h5452
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5453 | h5453
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5454 | h5454
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5455 | h5455
              · linarith only [h0, h5135, h5142, h5455, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5457 | h5457
                · linarith only [h5136, h5449, h5457, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5459 | h5459
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5460 | h5460
                    · linarith only [h5135, h5142, h5451, h5460, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5462 | h5462
                      · linarith only [h5136, h5449, h5452, h5462, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5464 | h5464
                        · linarith only [h5135, h5136, h5142, h5449, h5451, h5452, h5459, h5464, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases h2bigk with h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h0, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h0, h5459, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            rcases p5466_3 (m.d 0 2) (by simp) with h5470 | h5470
                            · rcases p5466_3 (m.d 1 2) (by simp) with h5471 | h5471
                              · rcases p5466_3 (m.d 2 3) (by simp) with h5472 | h5472
                                · linarith only [h5138, h5472, hlam]
                                · linarith only [h5459, h5472, hlam]
                              · linarith only [h5452, h5471, hlam]
                            · linarith only [h5470, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h0, h5459, h5460, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5459, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            rcases p5466_3 (m.d 0 2) (by simp) with h5481 | h5481
                            · linarith only [h0, h5481, hlam]
                            · linarith only [h5139, h5481, hlam]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5459, h5460, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5138, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5451, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5137, h5451, h5455, h5459, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5460, hlam, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5139, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5452, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5459, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5462, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5140, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h5453, hlam, p5466_0]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h0, h5140, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [h0, h5137, h5453, h5459, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5466_1]
                          · have p5466_0 := h5466c.1
                            have p5466_1 := h5466c.2.1
                            have p5466_2 := h5466c.2.2.1
                            have p5466_3 := h5466c.2.2.2
                            linarith only [hlam, p5466_0]
                  · linarith only [h5141, h5142, h5459, hc23, hc35, hlam, hphi]
            · linarith only [h5141, h5142, h5454, hc13, hc35, hlam, hphi]
          · linarith only [h0, h5140, h5453, hlam]
        · linarith only [h0, h5139, h5452, hlam]
      · linarith only [h0, h5138, h5451, hlam]

end R2N4
