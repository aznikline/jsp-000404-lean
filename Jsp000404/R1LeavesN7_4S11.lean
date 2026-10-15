import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7235 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h7237 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h7239 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 1 3 4 (by decide) (by decide) with h7474 | h7474
  · rcases m.htr 1 3 5 (by decide) (by decide) with h7475 | h7475
    · rcases m.htr 1 4 5 (by decide) (by decide) with h7476 | h7476
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7477 | h7477
        · rcases m.htr 2 3 5 (by decide) (by decide) with h7478 | h7478
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7479 | h7479
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7480 | h7480
              · rcases h1bigk with h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c | h7481c
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7483 | h7483
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7484 | h7484
                    · linarith only [h7484, hlam, p7481_0]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7486 | h7486
                      · linarith only [h1, h7486, hlam]
                      · linarith only [h7235, h7486, hlam]
                  · linarith only [h7483, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h7474, h7480, hc01, hc45, hlam, hphi, ht0b, ht5b, p7481_1]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7491 | h7491
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7492 | h7492
                    · linarith only [h0, h7492, hlam]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7494 | h7494
                      · linarith only [h1, h7494, hlam]
                      · linarith only [h7474, h7494, hlam]
                  · linarith only [h7491, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7498 | h7498
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7499 | h7499
                    · linarith only [h0, h7499, hlam]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7501 | h7501
                      · linarith only [h1, h7501, hlam]
                      · linarith only [h7475, h7501, hlam]
                  · linarith only [h7498, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h0, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h7235, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h7237, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h7239, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h1, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7511 | h7511
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7512 | h7512
                    · linarith only [h7235, h7512, hlam]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7514 | h7514
                      · rcases p7481_3 (m.d 1 4) (by simp) with h7515 | h7515
                        · linarith only [h7474, h7515, hlam]
                        · linarith only [h7237, h7515, hlam]
                      · linarith only [h7235, h7514, hlam]
                  · linarith only [h0, h7511, hlam]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h1, h7474, h7480, hc01, hc45, hlam, hphi, ht0b, ht5b, p7481_1]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7522 | h7522
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7523 | h7523
                    · linarith only [h7235, h7523, hlam]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7525 | h7525
                      · rcases p7481_3 (m.d 1 4) (by simp) with h7526 | h7526
                        · linarith only [h7474, h7526, hlam]
                        · linarith only [h7476, h7526, hlam]
                      · linarith only [h7475, h7525, hlam]
                  · linarith only [h3, h7522, hlam]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h2, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7532 | h7532
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7533 | h7533
                    · linarith only [h7237, h7533, hlam]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7535 | h7535
                      · rcases p7481_3 (m.d 1 4) (by simp) with h7536 | h7536
                        · rcases p7481_3 (m.d 1 5) (by simp) with h7537 | h7537
                          · linarith only [h7476, h7537, hlam]
                          · linarith only [h7239, h7537, hlam]
                        · linarith only [h7237, h7536, hlam]
                      · linarith only [h7235, h7535, hlam]
                  · linarith only [h0, h7532, hlam]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h7474, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7545 | h7545
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7546 | h7546
                    · linarith only [h7237, h7546, hlam]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7548 | h7548
                      · rcases p7481_3 (m.d 1 4) (by simp) with h7549 | h7549
                        · rcases p7481_3 (m.d 1 5) (by simp) with h7550 | h7550
                          · linarith only [h7476, h7550, hlam]
                          · rcases h3bigk with h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c | h7552c
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7239, h7474, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7481_1, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h4, hlam, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h4, h7480, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              rcases p7552_3 (m.d 0 3) (by simp) with h7557 | h7557
                              · rcases p7552_3 (m.d 1 3) (by simp) with h7558 | h7558
                                · linarith only [h1, h7558, hlam]
                                · linarith only [h7475, h7558, hlam]
                              · linarith only [h7557, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h1, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7235, hlam, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h1, h7480, hc01, hc45, hlam, hphi, ht0b, ht5b, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h1, h7239, h7474, hc12, hc23, hlam, hphi, p7481_1, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7239, h7474, hc12, hc23, hlam, hphi, p7481_1, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h1, h7239, h7474, h7480, hc01, hc12, hc23, hc45, hlam, hphi, ht0b, ht5b, p7481_1, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              rcases p7552_3 (m.d 0 3) (by simp) with h7571 | h7571
                              · linarith only [h4, h7571, hlam]
                              · linarith only [h7233, h7571, hlam]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7232, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7474, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7477, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7232, h7480, hc03, hc45, hlam, hphi, ht0b, ht5b, p7552_1]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7233, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7475, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7478, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [h7480, hlam, p7552_0]
                            · have p7552_0 := h7552c.1
                              have p7552_1 := h7552c.2.1
                              have p7552_2 := h7552c.2.2.1
                              have p7552_3 := h7552c.2.2.2
                              linarith only [hlam, p7552_0]
                        · linarith only [h7476, h7549, hlam]
                      · linarith only [h7475, h7548, hlam]
                  · linarith only [h3, h7545, hlam]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h3, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  rcases p7481_3 (m.d 0 1) (by simp) with h7588 | h7588
                  · rcases p7481_3 (m.d 1 2) (by simp) with h7589 | h7589
                    · linarith only [h7239, h7589, hlam]
                    · rcases p7481_3 (m.d 1 3) (by simp) with h7591 | h7591
                      · rcases p7481_3 (m.d 1 4) (by simp) with h7592 | h7592
                        · rcases p7481_3 (m.d 1 5) (by simp) with h7593 | h7593
                          · rcases h3bigk with h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c | h7594c
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h4, h7474, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h4, hlam, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h1, h4, h7474, h7476, h7480, hc01, hc12, hc23, hc45, hlam, hphi, ht0b, ht5b, p7481_1, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              rcases p7594_3 (m.d 0 3) (by simp) with h7599 | h7599
                              · rcases p7594_3 (m.d 1 3) (by simp) with h7600 | h7600
                                · linarith only [h1, h7600, hlam]
                                · linarith only [h7475, h7600, hlam]
                              · linarith only [h7599, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h1, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7235, hlam, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h1, h7480, hc01, hc45, hlam, hphi, ht0b, ht5b, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h1, h7480, hc01, hc45, hlam, hphi, ht0b, ht5b, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h1, h7474, h7476, hc12, hc23, hlam, hphi, p7481_1, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7474, h7476, hc12, hc23, hlam, hphi, p7481_1, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h1, h7474, h7476, h7480, hc01, hc12, hc23, hc45, hlam, hphi, ht0b, ht5b, p7481_1, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              rcases p7594_3 (m.d 0 3) (by simp) with h7613 | h7613
                              · linarith only [h4, h7613, hlam]
                              · linarith only [h7233, h7613, hlam]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7232, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7474, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7477, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7232, h7480, hc03, hc45, hlam, hphi, ht0b, ht5b, p7594_1]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7233, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7475, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7478, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [h7480, hlam, p7594_0]
                            · have p7594_0 := h7594c.1
                              have p7594_1 := h7594c.2.1
                              have p7594_2 := h7594c.2.2.1
                              have p7594_3 := h7594c.2.2.2
                              linarith only [hlam, p7594_0]
                          · linarith only [h7239, h7593, hlam]
                        · linarith only [h7237, h7592, hlam]
                      · linarith only [h7235, h7591, hlam]
                  · linarith only [h0, h7588, hlam]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h7475, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [h7476, hlam, p7481_0]
                · have p7481_0 := h7481c.1
                  have p7481_1 := h7481c.2.1
                  have p7481_2 := h7481c.2.2.1
                  have p7481_3 := h7481c.2.2.2
                  linarith only [hlam, p7481_0]
              · rcases h1bigk with h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c | h7633c
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  rcases p7633_3 (m.d 0 1) (by simp) with h7635 | h7635
                  · rcases p7633_3 (m.d 1 2) (by simp) with h7636 | h7636
                    · linarith only [h7636, hlam, p7633_0]
                    · rcases p7633_3 (m.d 1 3) (by simp) with h7638 | h7638
                      · linarith only [h1, h7638, hlam]
                      · linarith only [h7235, h7638, hlam]
                  · linarith only [h7635, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7474, h7476, h7480, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7633_1]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7476, h7480, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7633_1]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  rcases p7633_3 (m.d 0 1) (by simp) with h7644 | h7644
                  · rcases p7633_3 (m.d 1 2) (by simp) with h7645 | h7645
                    · linarith only [h0, h7645, hlam]
                    · rcases p7633_3 (m.d 1 3) (by simp) with h7647 | h7647
                      · linarith only [h1, h7647, hlam]
                      · linarith only [h7475, h7647, hlam]
                  · linarith only [h7644, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h0, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7235, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7237, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7239, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h1, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  rcases p7633_3 (m.d 0 1) (by simp) with h7657 | h7657
                  · rcases p7633_3 (m.d 1 2) (by simp) with h7658 | h7658
                    · linarith only [h7235, h7658, hlam]
                    · rcases p7633_3 (m.d 1 3) (by simp) with h7660 | h7660
                      · rcases p7633_3 (m.d 1 4) (by simp) with h7661 | h7661
                        · linarith only [h7474, h7661, hlam]
                        · linarith only [h7237, h7661, hlam]
                      · linarith only [h7235, h7660, hlam]
                  · linarith only [h0, h7657, hlam]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h1, h7476, h7480, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7633_1]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h1, h7476, h7480, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7633_1]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h2, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  rcases p7633_3 (m.d 0 1) (by simp) with h7670 | h7670
                  · rcases p7633_3 (m.d 1 2) (by simp) with h7671 | h7671
                    · linarith only [h7237, h7671, hlam]
                    · rcases p7633_3 (m.d 1 3) (by simp) with h7673 | h7673
                      · rcases p7633_3 (m.d 1 4) (by simp) with h7674 | h7674
                        · rcases p7633_3 (m.d 1 5) (by simp) with h7675 | h7675
                          · linarith only [h7476, h7675, hlam]
                          · linarith only [h7239, h7675, hlam]
                        · linarith only [h7237, h7674, hlam]
                      · linarith only [h7235, h7673, hlam]
                  · linarith only [h0, h7670, hlam]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7474, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h2, h7476, h7480, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7633_1]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h3, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  rcases p7633_3 (m.d 0 1) (by simp) with h7685 | h7685
                  · rcases p7633_3 (m.d 1 2) (by simp) with h7686 | h7686
                    · linarith only [h7239, h7686, hlam]
                    · rcases p7633_3 (m.d 1 3) (by simp) with h7688 | h7688
                      · rcases p7633_3 (m.d 1 4) (by simp) with h7689 | h7689
                        · rcases p7633_3 (m.d 1 5) (by simp) with h7690 | h7690
                          · rcases h3bigk with h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c | h7691c
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h4, h7474, h7476, hc12, hc23, hlam, hphi, p7633_1, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h4, hlam, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              rcases p7691_3 (m.d 0 3) (by simp) with h7695 | h7695
                              · rcases p7691_3 (m.d 1 3) (by simp) with h7696 | h7696
                                · linarith only [h1, h7696, hlam]
                                · linarith only [h7474, h7696, hlam]
                              · linarith only [h7695, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              rcases p7691_3 (m.d 0 3) (by simp) with h7700 | h7700
                              · rcases p7691_3 (m.d 1 3) (by simp) with h7701 | h7701
                                · linarith only [h1, h7701, hlam]
                                · linarith only [h7475, h7701, hlam]
                              · linarith only [h7700, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h1, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7235, hlam, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h1, h7480, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h1, h7474, h7476, hc12, hc23, hlam, hphi, p7633_1, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7474, h7476, hc12, hc23, hlam, hphi, p7633_1, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              rcases p7691_3 (m.d 0 3) (by simp) with h7713 | h7713
                              · linarith only [h4, h7713, hlam]
                              · linarith only [h7232, h7713, hlam]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              rcases p7691_3 (m.d 0 3) (by simp) with h7716 | h7716
                              · linarith only [h4, h7716, hlam]
                              · linarith only [h7233, h7716, hlam]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7232, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7474, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7477, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7480, hlam, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7233, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7475, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7478, hlam, p7691_0]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [h7233, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7691_1]
                            · have p7691_0 := h7691c.1
                              have p7691_1 := h7691c.2.1
                              have p7691_2 := h7691c.2.2.1
                              have p7691_3 := h7691c.2.2.2
                              linarith only [hlam, p7691_0]
                          · linarith only [h7239, h7690, hlam]
                        · linarith only [h7237, h7689, hlam]
                      · linarith only [h7235, h7688, hlam]
                  · linarith only [h0, h7685, hlam]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7475, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [h7476, hlam, p7633_0]
                · have p7633_0 := h7633c.1
                  have p7633_1 := h7633c.2.1
                  have p7633_2 := h7633c.2.2.1
                  have p7633_3 := h7633c.2.2.2
                  linarith only [hlam, p7633_0]
            · linarith only [h6364, h7234, h7479, hlam]
          · linarith only [h1, h4, h7475, h7478, hlam]
        · linarith only [h0, h1, h4, h7474, h7477, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7739 | h7739
        · rcases m.htr 2 3 5 (by decide) (by decide) with h7740 | h7740
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7741 | h7741
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7742 | h7742
              · linarith only [h7474, h7476, h7742, hlam]
              · rcases h1bigk with h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c | h7744c
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  rcases p7744_3 (m.d 0 1) (by simp) with h7746 | h7746
                  · rcases p7744_3 (m.d 1 2) (by simp) with h7747 | h7747
                    · linarith only [h7747, hlam, p7744_0]
                    · rcases p7744_3 (m.d 1 3) (by simp) with h7749 | h7749
                      · linarith only [h1, h7749, hlam]
                      · linarith only [h7235, h7749, hlam]
                  · linarith only [h7746, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  rcases p7744_3 (m.d 0 1) (by simp) with h7753 | h7753
                  · rcases p7744_3 (m.d 1 2) (by simp) with h7754 | h7754
                    · linarith only [h0, h7754, hlam]
                    · rcases p7744_3 (m.d 1 3) (by simp) with h7756 | h7756
                      · linarith only [h7756, hlam, p7744_0]
                      · rcases p7744_3 (m.d 1 4) (by simp) with h7758 | h7758
                        · linarith only [h2, h7758, hlam]
                        · rcases p7744_3 (m.d 1 5) (by simp) with h7760 | h7760
                          · linarith only [h3, h7760, hlam]
                          · rcases h3bigk with h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c | h7762c
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h1, hlam, p7744_2, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h4, hlam, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              rcases p7762_3 (m.d 0 3) (by simp) with h7766 | h7766
                              · rcases p7762_3 (m.d 1 3) (by simp) with h7767 | h7767
                                · linarith only [h1, h7767, hlam]
                                · linarith only [h7474, h7767, hlam]
                              · linarith only [h7766, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              rcases p7762_3 (m.d 0 3) (by simp) with h7771 | h7771
                              · rcases p7762_3 (m.d 1 3) (by simp) with h7772 | h7772
                                · linarith only [h1, h7772, hlam]
                                · linarith only [h7475, h7772, hlam]
                              · linarith only [h7771, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h1, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7235, hlam, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7744_1, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7742, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7744_1, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7235, hc12, hc23, hlam, hphi, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              rcases p7762_3 (m.d 0 3) (by simp) with h7784 | h7784
                              · linarith only [h4, h7784, hlam]
                              · linarith only [h7232, h7784, hlam]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              rcases p7762_3 (m.d 0 3) (by simp) with h7787 | h7787
                              · linarith only [h4, h7787, hlam]
                              · linarith only [h7233, h7787, hlam]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7232, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7474, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7739, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7742, hlam, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7233, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7475, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7740, hlam, p7762_0]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [h7475, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7762_1]
                            · have p7762_0 := h7762c.1
                              have p7762_1 := h7762c.2.1
                              have p7762_2 := h7762c.2.2.1
                              have p7762_3 := h7762c.2.2.2
                              linarith only [hlam, p7762_0]
                  · linarith only [h7753, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  rcases p7744_3 (m.d 0 1) (by simp) with h7801 | h7801
                  · rcases p7744_3 (m.d 1 2) (by simp) with h7802 | h7802
                    · linarith only [h0, h7802, hlam]
                    · rcases p7744_3 (m.d 1 3) (by simp) with h7804 | h7804
                      · linarith only [h1, h7804, hlam]
                      · linarith only [h7474, h7804, hlam]
                  · linarith only [h7801, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  rcases p7744_3 (m.d 0 1) (by simp) with h7808 | h7808
                  · rcases p7744_3 (m.d 1 2) (by simp) with h7809 | h7809
                    · linarith only [h0, h7809, hlam]
                    · rcases p7744_3 (m.d 1 3) (by simp) with h7811 | h7811
                      · linarith only [h1, h7811, hlam]
                      · linarith only [h7475, h7811, hlam]
                  · linarith only [h7808, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h0, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h7235, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h7237, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h7239, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h1, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  rcases p7744_3 (m.d 0 1) (by simp) with h7821 | h7821
                  · rcases p7744_3 (m.d 1 2) (by simp) with h7822 | h7822
                    · linarith only [h7235, h7822, hlam]
                    · rcases p7744_3 (m.d 1 3) (by simp) with h7824 | h7824
                      · rcases p7744_3 (m.d 1 4) (by simp) with h7825 | h7825
                        · linarith only [h7474, h7825, hlam]
                        · linarith only [h7237, h7825, hlam]
                      · linarith only [h7235, h7824, hlam]
                  · linarith only [h0, h7821, hlam]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  rcases p7744_3 (m.d 0 1) (by simp) with h7831 | h7831
                  · rcases p7744_3 (m.d 1 2) (by simp) with h7832 | h7832
                    · linarith only [h7235, h7832, hlam]
                    · rcases p7744_3 (m.d 1 3) (by simp) with h7834 | h7834
                      · rcases p7744_3 (m.d 1 4) (by simp) with h7835 | h7835
                        · linarith only [h7474, h7835, hlam]
                        · rcases p7744_3 (m.d 1 5) (by simp) with h7837 | h7837
                          · linarith only [h7475, h7837, hlam]
                          · linarith only [h7476, h7837, hlam]
                      · linarith only [h7474, h7834, hlam]
                  · linarith only [h2, h7831, hlam]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  rcases p7744_3 (m.d 0 1) (by simp) with h7842 | h7842
                  · rcases p7744_3 (m.d 1 2) (by simp) with h7843 | h7843
                    · linarith only [h7235, h7843, hlam]
                    · rcases p7744_3 (m.d 1 3) (by simp) with h7845 | h7845
                      · rcases p7744_3 (m.d 1 4) (by simp) with h7846 | h7846
                        · linarith only [h7474, h7846, hlam]
                        · rcases p7744_3 (m.d 1 5) (by simp) with h7848 | h7848
                          · linarith only [h7475, h7848, hlam]
                          · rcases h3bigk with h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c | h7850c
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7237, h7476, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7744_1, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h4, hlam, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              rcases p7850_3 (m.d 0 3) (by simp) with h7854 | h7854
                              · rcases p7850_3 (m.d 1 3) (by simp) with h7855 | h7855
                                · linarith only [h1, h7855, hlam]
                                · linarith only [h7474, h7855, hlam]
                              · linarith only [h7854, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              rcases p7850_3 (m.d 0 3) (by simp) with h7859 | h7859
                              · rcases p7850_3 (m.d 1 3) (by simp) with h7860 | h7860
                                · linarith only [h1, h7860, hlam]
                                · linarith only [h7475, h7860, hlam]
                              · linarith only [h7859, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h1, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7235, hlam, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h1, h7742, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7235, hc12, hc23, hlam, hphi, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              rcases p7850_3 (m.d 0 3) (by simp) with h7872 | h7872
                              · linarith only [h4, h7872, hlam]
                              · linarith only [h7232, h7872, hlam]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              rcases p7850_3 (m.d 0 3) (by simp) with h7875 | h7875
                              · linarith only [h4, h7875, hlam]
                              · linarith only [h7233, h7875, hlam]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7232, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7474, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7739, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7742, hlam, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7233, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7475, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7740, hlam, p7850_0]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [h7233, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7850_1]
                            · have p7850_0 := h7850c.1
                              have p7850_1 := h7850c.2.1
                              have p7850_2 := h7850c.2.2.1
                              have p7850_3 := h7850c.2.2.2
                              linarith only [hlam, p7850_0]
                      · linarith only [h7475, h7845, hlam]
                  · linarith only [h3, h7842, hlam]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h2, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h7234, h7476, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7744_1]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h7474, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h7476, hlam, p7744_1]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h3, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h6364, h7234, h7476, h7739, hc12, hc23, hlam, hphi, p7744_1]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h7475, hlam, p7744_0]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [h6364, h7234, h7237, h7476, h7739, hc12, hc23, hlam, hphi, p7744_1]
                · have p7744_0 := h7744c.1
                  have p7744_1 := h7744c.2.1
                  have p7744_2 := h7744c.2.2.1
                  have p7744_3 := h7744c.2.2.2
                  linarith only [hlam, p7744_0]
            · linarith only [h6364, h7234, h7741, hlam]
          · linarith only [h1, h6364, h7234, h7475, h7476, h7739, h7740, hc01, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h4, h7232, h7234, h7237, h7474, h7476, h7739, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h7903 | h7903
      · linarith only [h7474, h7475, h7903, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7905 | h7905
        · rcases m.htr 2 3 5 (by decide) (by decide) with h7906 | h7906
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7907 | h7907
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7908 | h7908
              · linarith only [h4, h7233, h7237, h7474, h7475, h7903, h7908, hc12, hc23, hlam, hphi]
              · rcases h1bigk with h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  rcases p7910_3 (m.d 0 1) (by simp) with h7912 | h7912
                  · rcases p7910_3 (m.d 1 2) (by simp) with h7913 | h7913
                    · linarith only [h7913, hlam, p7910_0]
                    · rcases p7910_3 (m.d 1 3) (by simp) with h7915 | h7915
                      · linarith only [h1, h7915, hlam]
                      · linarith only [h7235, h7915, hlam]
                  · linarith only [h7912, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  rcases p7910_3 (m.d 0 1) (by simp) with h7919 | h7919
                  · rcases p7910_3 (m.d 1 2) (by simp) with h7920 | h7920
                    · linarith only [h0, h7920, hlam]
                    · rcases p7910_3 (m.d 1 3) (by simp) with h7922 | h7922
                      · linarith only [h7922, hlam, p7910_0]
                      · rcases p7910_3 (m.d 1 4) (by simp) with h7924 | h7924
                        · linarith only [h2, h7924, hlam]
                        · rcases p7910_3 (m.d 1 5) (by simp) with h7926 | h7926
                          · linarith only [h3, h7926, hlam]
                          · linarith only [h7475, h7926, hlam]
                  · linarith only [h7919, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  rcases p7910_3 (m.d 0 1) (by simp) with h7930 | h7930
                  · rcases p7910_3 (m.d 1 2) (by simp) with h7931 | h7931
                    · linarith only [h0, h7931, hlam]
                    · rcases p7910_3 (m.d 1 3) (by simp) with h7933 | h7933
                      · linarith only [h1, h7933, hlam]
                      · linarith only [h7474, h7933, hlam]
                  · linarith only [h7930, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  rcases p7910_3 (m.d 0 1) (by simp) with h7937 | h7937
                  · rcases p7910_3 (m.d 1 2) (by simp) with h7938 | h7938
                    · linarith only [h0, h7938, hlam]
                    · rcases p7910_3 (m.d 1 3) (by simp) with h7940 | h7940
                      · linarith only [h1, h7940, hlam]
                      · rcases p7910_3 (m.d 1 4) (by simp) with h7942 | h7942
                        · linarith only [h2, h7942, hlam]
                        · rcases p7910_3 (m.d 1 5) (by simp) with h7944 | h7944
                          · linarith only [h7944, hlam, p7910_0]
                          · rcases h3bigk with h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c | h7946c
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h4, h7474, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h4, hlam, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              rcases p7946_3 (m.d 0 3) (by simp) with h7950 | h7950
                              · rcases p7946_3 (m.d 1 3) (by simp) with h7951 | h7951
                                · linarith only [h1, h7951, hlam]
                                · linarith only [h7474, h7951, hlam]
                              · linarith only [h7950, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h4, h7474, h7475, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h1, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7235, hlam, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7234, h7475, h7908, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7475, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h0, h4, hc12, hc23, hlam, hphi, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7235, hc12, hc23, hlam, hphi, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              rcases p7946_3 (m.d 0 3) (by simp) with h7964 | h7964
                              · linarith only [h4, h7964, hlam]
                              · linarith only [h7232, h7964, hlam]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7474, h7475, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7232, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7474, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7905, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7908, hlam, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7233, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7474, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h7906, hlam, p7946_0]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [h4, h7232, h7234, h7908, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7946_1]
                            · have p7946_0 := h7946c.1
                              have p7946_1 := h7946c.2.1
                              have p7946_2 := h7946c.2.2.1
                              have p7946_3 := h7946c.2.2.2
                              linarith only [hlam, p7946_0]
                  · linarith only [h7937, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h0, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h7235, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h7237, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h7239, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h1, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h4, h7232, h7234, h7475, h7908, hc12, hc23, hlam, hphi, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h4, h7232, h7234, h7237, h7475, h7908, hc12, hc23, hlam, hphi, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h7475, hlam, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h2, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h4, h7232, h7234, h7474, h7475, h7908, hc12, hc23, hlam, hphi, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h7474, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h7903, hlam, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h3, hlam, p7910_0]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h4, h7232, h7234, h7475, h7908, hc12, hc23, hlam, hphi, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h4, h7232, h7234, h7474, h7475, h7908, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [h4, h7232, h7234, h7237, h7475, h7908, hc12, hc23, hlam, hphi, p7910_1]
                · have p7910_0 := h7910c.1
                  have p7910_1 := h7910c.2.1
                  have p7910_2 := h7910c.2.2.1
                  have p7910_3 := h7910c.2.2.2
                  linarith only [hlam, p7910_0]
            · linarith only [h0, h4, h6364, h7232, h7234, h7907, hc12, hc23, hlam, hphi]
          · linarith only [h4, h7233, h7906, hlam]
        · linarith only [h1, h4, h7232, h7234, h7474, h7903, h7905, hc01, hc15, hlam, hphi, ht0b, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h8002 | h8002
    · rcases m.htr 1 4 5 (by decide) (by decide) with h8003 | h8003
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8004 | h8004
        · rcases m.htr 2 3 5 (by decide) (by decide) with h8005 | h8005
          · rcases m.htr 2 4 5 (by decide) (by decide) with h8006 | h8006
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8007 | h8007
              · rcases h1bigk with h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  rcases p8008_3 (m.d 0 1) (by simp) with h8010 | h8010
                  · rcases p8008_3 (m.d 1 2) (by simp) with h8011 | h8011
                    · linarith only [h8011, hlam, p8008_0]
                    · rcases p8008_3 (m.d 1 3) (by simp) with h8013 | h8013
                      · linarith only [h1, h8013, hlam]
                      · linarith only [h7235, h8013, hlam]
                  · linarith only [h8010, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  rcases p8008_3 (m.d 0 1) (by simp) with h8017 | h8017
                  · rcases p8008_3 (m.d 1 2) (by simp) with h8018 | h8018
                    · linarith only [h0, h8018, hlam]
                    · rcases p8008_3 (m.d 1 3) (by simp) with h8020 | h8020
                      · linarith only [h8020, hlam, p8008_0]
                      · rcases p8008_3 (m.d 1 4) (by simp) with h8022 | h8022
                        · linarith only [h2, h8022, hlam]
                        · linarith only [h7474, h8022, hlam]
                  · linarith only [h8017, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  rcases p8008_3 (m.d 0 1) (by simp) with h8026 | h8026
                  · rcases p8008_3 (m.d 1 2) (by simp) with h8027 | h8027
                    · linarith only [h0, h8027, hlam]
                    · rcases p8008_3 (m.d 1 3) (by simp) with h8029 | h8029
                      · linarith only [h1, h8029, hlam]
                      · rcases p8008_3 (m.d 1 4) (by simp) with h8031 | h8031
                        · linarith only [h8031, hlam, p8008_0]
                        · rcases p8008_3 (m.d 1 5) (by simp) with h8033 | h8033
                          · linarith only [h3, h8033, hlam]
                          · rcases h3bigk with h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h8002, h8007, hc03, hc45, hlam, hphi, ht0b, ht5b, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h4, hlam, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h4, h7474, h8002, h8007, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              rcases p8035_3 (m.d 0 3) (by simp) with h8040 | h8040
                              · rcases p8035_3 (m.d 1 3) (by simp) with h8041 | h8041
                                · linarith only [h1, h8041, hlam]
                                · linarith only [h8002, h8041, hlam]
                              · linarith only [h8040, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h1, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h7235, hlam, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h7474, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h7232, h7474, h8007, hc04, hc45, hlam, hphi, ht0b, ht5b, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h1, h7239, h8002, hc12, hc23, hlam, hphi, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h7239, h8002, hc12, hc23, hlam, hphi, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h7474, h8002, h8007, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              rcases p8035_3 (m.d 0 3) (by simp) with h8054 | h8054
                              · linarith only [h4, h8054, hlam]
                              · linarith only [h7233, h8054, hlam]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h7232, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h8002, h8007, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h8004, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h4, h7232, h8007, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8035_1]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h7233, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h8002, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h8005, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [h8007, hlam, p8035_0]
                            · have p8035_0 := h8035c.1
                              have p8035_1 := h8035c.2.1
                              have p8035_2 := h8035c.2.2.1
                              have p8035_3 := h8035c.2.2.2
                              linarith only [hlam, p8035_0]
                  · linarith only [h8026, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  rcases p8008_3 (m.d 0 1) (by simp) with h8068 | h8068
                  · rcases p8008_3 (m.d 1 2) (by simp) with h8069 | h8069
                    · linarith only [h0, h8069, hlam]
                    · rcases p8008_3 (m.d 1 3) (by simp) with h8071 | h8071
                      · linarith only [h1, h8071, hlam]
                      · linarith only [h8002, h8071, hlam]
                  · linarith only [h8068, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h0, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h7235, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h7237, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h7239, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h1, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h4, h7232, h7474, hc12, hc23, hlam, hphi, p8008_1]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h7474, hlam, p8008_1]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h4, h7232, h7239, h7474, hc12, hc23, hlam, hphi, p8008_1]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h2, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h4, h7232, h7474, hc12, hc23, hlam, hphi, p8008_1]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h4, h7232, h7235, h7474, hc12, hc23, hlam, hphi, p8008_1]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h4, h7232, h7239, h7474, hc12, hc23, hlam, hphi, p8008_1]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h3, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h4, h7232, h7474, h8002, hc12, hc23, hlam, hphi, p8008_1]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h8002, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [h8003, hlam, p8008_0]
                · have p8008_0 := h8008c.1
                  have p8008_1 := h8008c.2.1
                  have p8008_2 := h8008c.2.2.1
                  have p8008_3 := h8008c.2.2.2
                  linarith only [hlam, p8008_0]
              · linarith only [h4, h7232, h7234, h7235, h7474, h8007, hc12, hc23, hlam, hphi]
            · linarith only [h0, h6364, h7474, h8002, h8003, h8006, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h4, h7232, h7474, h8005, hc13, hc35, hlam, hphi]
        · linarith only [h4, h7232, h8004, hlam]
      · linarith only [h7474, h8002, h8003, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h8100 | h8100
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8101 | h8101
        · rcases m.htr 2 3 5 (by decide) (by decide) with h8102 | h8102
          · rcases m.htr 2 4 5 (by decide) (by decide) with h8103 | h8103
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8104 | h8104
              · rcases h1bigk with h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c | h8105c
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  rcases p8105_3 (m.d 0 1) (by simp) with h8107 | h8107
                  · rcases p8105_3 (m.d 1 2) (by simp) with h8108 | h8108
                    · linarith only [h8108, hlam, p8105_0]
                    · rcases p8105_3 (m.d 1 3) (by simp) with h8110 | h8110
                      · linarith only [h1, h8110, hlam]
                      · linarith only [h7235, h8110, hlam]
                  · linarith only [h8107, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  rcases p8105_3 (m.d 0 1) (by simp) with h8114 | h8114
                  · rcases p8105_3 (m.d 1 2) (by simp) with h8115 | h8115
                    · linarith only [h0, h8115, hlam]
                    · rcases p8105_3 (m.d 1 3) (by simp) with h8117 | h8117
                      · linarith only [h8117, hlam, p8105_0]
                      · rcases p8105_3 (m.d 1 4) (by simp) with h8119 | h8119
                        · linarith only [h2, h8119, hlam]
                        · linarith only [h7474, h8119, hlam]
                  · linarith only [h8114, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  rcases p8105_3 (m.d 0 1) (by simp) with h8123 | h8123
                  · rcases p8105_3 (m.d 1 2) (by simp) with h8124 | h8124
                    · linarith only [h0, h8124, hlam]
                    · rcases p8105_3 (m.d 1 3) (by simp) with h8126 | h8126
                      · linarith only [h1, h8126, hlam]
                      · rcases p8105_3 (m.d 1 4) (by simp) with h8128 | h8128
                        · linarith only [h8128, hlam, p8105_0]
                        · rcases p8105_3 (m.d 1 5) (by simp) with h8130 | h8130
                          · linarith only [h3, h8130, hlam]
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
                              linarith only [h4, h7235, hc12, hc23, hlam, hphi, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h4, hlam, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h4, h7235, h7474, hc12, hc23, hlam, hphi, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h4, h7235, h8002, hc12, hc23, hlam, hphi, p8132_1]
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
                              linarith only [h7235, hlam, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7474, hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h8002, hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h1, h7235, hc12, hc23, hlam, hphi, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7235, hc12, hc23, hlam, hphi, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7235, h7474, hc12, hc23, hlam, hphi, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7235, h8002, hc12, hc23, hlam, hphi, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7232, hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7235, hc12, hc34, hlam, hphi, ht23, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h8101, hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7232, h7235, h8002, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7233, hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h7235, hc12, hc35, hlam, hphi, ht23, p8132_1]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h8102, hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [h8104, hlam, p8132_0]
                            · have p8132_0 := h8132c.1
                              have p8132_1 := h8132c.2.1
                              have p8132_2 := h8132c.2.2.1
                              have p8132_3 := h8132c.2.2.2
                              linarith only [hlam, p8132_0]
                  · linarith only [h8123, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  rcases p8105_3 (m.d 0 1) (by simp) with h8159 | h8159
                  · rcases p8105_3 (m.d 1 2) (by simp) with h8160 | h8160
                    · linarith only [h0, h8160, hlam]
                    · rcases p8105_3 (m.d 1 3) (by simp) with h8162 | h8162
                      · linarith only [h1, h8162, hlam]
                      · rcases p8105_3 (m.d 1 4) (by simp) with h8164 | h8164
                        · linarith only [h2, h8164, hlam]
                        · linarith only [h8100, h8164, hlam]
                  · linarith only [h8159, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h0, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h7235, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h7237, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h7239, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h1, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h4, h7232, h7474, hc12, hc23, hlam, hphi, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h7474, hlam, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h8002, hlam, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h2, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h4, h7232, h7474, hc12, hc23, hlam, hphi, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h4, h7232, h7235, h7474, hc12, hc23, hlam, hphi, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h4, h7232, h7235, h7474, h8002, hc12, hc23, hlam, hphi, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h3, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h4, h7232, h8002, h8104, hc12, hc23, hlam, hphi, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h4, h7232, h7235, h8002, h8104, hc12, hc23, hlam, hphi, p8105_1]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [h8100, hlam, p8105_0]
                · have p8105_0 := h8105c.1
                  have p8105_1 := h8105c.2.1
                  have p8105_2 := h8105c.2.2.1
                  have p8105_3 := h8105c.2.2.2
                  linarith only [hlam, p8105_0]
              · linarith only [h4, h7232, h7234, h7235, h7474, h8104, hc12, hc23, hlam, hphi]
            · linarith only [h0, h6364, h7474, h8100, h8103, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h4, h7233, h8102, hlam]
        · linarith only [h4, h7232, h8101, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8192 | h8192
        · rcases m.htr 2 3 5 (by decide) (by decide) with h8193 | h8193
          · rcases m.htr 2 4 5 (by decide) (by decide) with h8194 | h8194
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8195 | h8195
              · linarith only [h4, h7232, h7237, h8100, h8195, hc12, hc23, hlam, hphi]
              · linarith only [h4, h7232, h7234, h7235, h7474, h8195, hc12, hc23, hlam, hphi]
            · linarith only [h6364, h7234, h8194, hlam]
          · linarith only [h4, h7233, h8193, hlam]
        · linarith only [h4, h7232, h8192, hlam]

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7235 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h7237 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 1 2 5 (by decide) (by decide) with h7239 | h7239
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234 h7235 h7237 h7239
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234 h7235 h7237 h7239

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7235 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 1 2 4 (by decide) (by decide) with h7237 | h7237
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234 h7235 h7237
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234 h7235 h7237

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 1 2 3 (by decide) (by decide) with h7235 | h7235
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234 h7235
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234 h7235

end R2N4
