import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8476 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8478 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h8480 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases h0bigk with h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c | h8481c
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h0, hlam, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    rcases p8481_3 (m.d 0 1) (by simp) with h8484 | h8484
    · rcases p8481_3 (m.d 0 2) (by simp) with h8485 | h8485
      · rcases p8481_3 (m.d 0 3) (by simp) with h8486 | h8486
        · linarith only [h6793, h8486, hlam]
        · rcases p8481_3 (m.d 0 4) (by simp) with h8488 | h8488
          · linarith only [h6794, h8488, hlam]
          · linarith only [h6799, h8488, hlam]
      · linarith only [h6796, h8485, hlam]
    · linarith only [h6793, h8484, hlam]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    rcases p8481_3 (m.d 0 1) (by simp) with h8493 | h8493
    · rcases p8481_3 (m.d 0 2) (by simp) with h8494 | h8494
      · rcases p8481_3 (m.d 0 3) (by simp) with h8495 | h8495
        · linarith only [h6793, h8495, hlam]
        · rcases p8481_3 (m.d 0 4) (by simp) with h8497 | h8497
          · linarith only [h6794, h8497, hlam]
          · rcases p8481_3 (m.d 0 5) (by simp) with h8499 | h8499
            · linarith only [h6795, h8499, hlam]
            · linarith only [h7593, h8499, hlam]
      · linarith only [h6797, h8494, hlam]
    · linarith only [h6794, h8493, hlam]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    rcases p8481_3 (m.d 0 1) (by simp) with h8504 | h8504
    · rcases p8481_3 (m.d 0 2) (by simp) with h8505 | h8505
      · rcases p8481_3 (m.d 0 3) (by simp) with h8506 | h8506
        · linarith only [h6793, h8506, hlam]
        · rcases p8481_3 (m.d 0 4) (by simp) with h8508 | h8508
          · linarith only [h6794, h8508, hlam]
          · rcases p8481_3 (m.d 0 5) (by simp) with h8510 | h8510
            · linarith only [h6795, h8510, hlam]
            · rcases h0emin with h8512 | h8512 | h8512 | h8512 | h8512
              · rcases h2bigk with h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c | h8513c
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h0, hlam, p8513_1]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  rcases p8513_3 (m.d 0 2) (by simp) with h8516 | h8516
                  · rcases p8513_3 (m.d 1 2) (by simp) with h8517 | h8517
                    · rcases p8513_3 (m.d 2 3) (by simp) with h8518 | h8518
                      · linarith only [h8518, hlam, p8513_0]
                      · rcases p8513_3 (m.d 2 4) (by simp) with h8520 | h8520
                        · linarith only [h6797, h8520, hlam]
                        · linarith only [h8474, h8520, hlam]
                    · linarith only [h8467, h8517, hlam]
                  · linarith only [h8516, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  rcases p8513_3 (m.d 0 2) (by simp) with h8525 | h8525
                  · rcases p8513_3 (m.d 1 2) (by simp) with h8526 | h8526
                    · rcases p8513_3 (m.d 2 3) (by simp) with h8527 | h8527
                      · linarith only [h6796, h8527, hlam]
                      · rcases p8513_3 (m.d 2 4) (by simp) with h8529 | h8529
                        · linarith only [h8529, hlam, p8513_0]
                        · rcases p8513_3 (m.d 2 5) (by simp) with h8531 | h8531
                          · linarith only [h6798, h8531, hlam]
                          · linarith only [h8478, h8531, hlam]
                    · linarith only [h8468, h8526, hlam]
                  · linarith only [h8525, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  rcases p8513_3 (m.d 0 2) (by simp) with h8536 | h8536
                  · rcases p8513_3 (m.d 1 2) (by simp) with h8537 | h8537
                    · rcases p8513_3 (m.d 2 3) (by simp) with h8538 | h8538
                      · linarith only [h6796, h8538, hlam]
                      · rcases p8513_3 (m.d 2 4) (by simp) with h8540 | h8540
                        · linarith only [h6797, h8540, hlam]
                        · rcases p8513_3 (m.d 2 5) (by simp) with h8542 | h8542
                          · linarith only [h8542, hlam, p8513_0]
                          · rcases h4bigk with h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h7593, hc14, hlam, hphi, ht0b, ht45, ht5b, p8481_1, p8544_1, u0elo0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h0, h7593, h8474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8481_1, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h6799, hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h7593, hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h6794, hlam, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h0, h6794, h8474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8470, hlam, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8472, hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h6797, hlam, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8468, hlam, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8474, hlam, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8478, hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              rcases p8544_3 (m.d 0 4) (by simp) with h8560 | h8560
                              · linarith only [h6799, h8560, hlam]
                              · rcases p8544_3 (m.d 1 4) (by simp) with h8562 | h8562
                                · linarith only [h8470, h8562, hlam]
                                · rcases p8544_3 (m.d 2 4) (by simp) with h8564 | h8564
                                  · linarith only [h8474, h8564, hlam]
                                  · rcases p8544_3 (m.d 3 4) (by simp) with h8566 | h8566
                                    · rcases p8544_3 (m.d 4 5) (by simp) with h8567 | h8567
                                      · linarith only [h8480, h8567, hlam]
                                      · linarith only [h7593, h8567, hlam]
                                    · linarith only [h6799, h8566, hlam]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              rcases p8544_3 (m.d 0 4) (by simp) with h8571 | h8571
                              · linarith only [h6799, h8571, hlam]
                              · linarith only [h6794, h8571, hlam]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              rcases p8544_3 (m.d 0 4) (by simp) with h8574 | h8574
                              · linarith only [h6799, h8574, hlam]
                              · linarith only [h6797, h8574, hlam]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h6799, h7593, hc03, hc34, hlam, hphi, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h6793, h6799, h8467, h8480, hc23, hc34, hlam, hphi, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8468, h8474, h8480, hc23, hc34, hlam, hphi, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8474, h8480, hc23, hc34, hlam, hphi, p8544_1]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [h8480, hlam, p8544_0]
                            · have p8544_0 := h8544c.1
                              have p8544_1 := h8544c.2.1
                              have p8544_2 := h8544c.2.2.1
                              have p8544_3 := h8544c.2.2.2
                              linarith only [hlam, p8544_0]
                    · linarith only [h8469, h8537, hlam]
                  · linarith only [h8536, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h0, h6793, h6799, h7593, h8467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8481_1, p8513_1]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h0, h6793, h6799, h7593, h8467, hlam, p8481_1, p8513_2]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h0, h6794, h7593, h8468, hlam, p8481_1, p8513_2]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h0, h6798, hlam, p8481_1, p8513_2]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h6796, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h8467, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h8474, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h8476, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h6797, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h8468, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h6794, h7593, h8468, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8481_1, p8513_1, u0elo0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h8478, hlam, p8513_1]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h6798, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h8469, hlam, p8513_0]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h0, h6795, h8469, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8481_1, p8513_1, u0elo1]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [h0, h6795, h8469, hc24, hlam, hphi, ht0b, ht45, ht5b, p8481_1, p8513_1, u0elo1]
                · have p8513_0 := h8513c.1
                  have p8513_1 := h8513c.2.1
                  have p8513_2 := h8513c.2.2.1
                  have p8513_3 := h8513c.2.2.2
                  linarith only [hlam, p8513_0]
              · rcases h2bigk with h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c | h8606c
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h0, hlam, p8606_1]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  rcases p8606_3 (m.d 0 2) (by simp) with h8609 | h8609
                  · rcases p8606_3 (m.d 1 2) (by simp) with h8610 | h8610
                    · rcases p8606_3 (m.d 2 3) (by simp) with h8611 | h8611
                      · linarith only [h8611, hlam, p8606_0]
                      · rcases p8606_3 (m.d 2 4) (by simp) with h8613 | h8613
                        · linarith only [h6797, h8613, hlam]
                        · linarith only [h8474, h8613, hlam]
                    · linarith only [h8467, h8610, hlam]
                  · linarith only [h8609, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  rcases p8606_3 (m.d 0 2) (by simp) with h8618 | h8618
                  · rcases p8606_3 (m.d 1 2) (by simp) with h8619 | h8619
                    · rcases p8606_3 (m.d 2 3) (by simp) with h8620 | h8620
                      · linarith only [h6796, h8620, hlam]
                      · rcases p8606_3 (m.d 2 4) (by simp) with h8622 | h8622
                        · linarith only [h8622, hlam, p8606_0]
                        · rcases p8606_3 (m.d 2 5) (by simp) with h8624 | h8624
                          · linarith only [h6798, h8624, hlam]
                          · linarith only [h8478, h8624, hlam]
                    · linarith only [h8468, h8619, hlam]
                  · linarith only [h8618, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  rcases p8606_3 (m.d 0 2) (by simp) with h8629 | h8629
                  · rcases p8606_3 (m.d 1 2) (by simp) with h8630 | h8630
                    · rcases p8606_3 (m.d 2 3) (by simp) with h8631 | h8631
                      · linarith only [h6796, h8631, hlam]
                      · rcases p8606_3 (m.d 2 4) (by simp) with h8633 | h8633
                        · linarith only [h6797, h8633, hlam]
                        · rcases p8606_3 (m.d 2 5) (by simp) with h8635 | h8635
                          · linarith only [h8635, hlam, p8606_0]
                          · rcases h4bigk with h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c | h8637c
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h0, h7593, hc14, hlam, hphi, ht0b, ht45, ht5b, p8481_1, p8637_1, u0elo1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h0, h7593, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8481_1, p8637_1, u0elo1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h6799, hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h7593, hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h6794, hlam, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h0, h6794, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8637_1, u0elo1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8470, hlam, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8472, hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h6797, hlam, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8468, hlam, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8474, hlam, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8478, hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              rcases p8637_3 (m.d 0 4) (by simp) with h8653 | h8653
                              · linarith only [h6799, h8653, hlam]
                              · rcases p8637_3 (m.d 1 4) (by simp) with h8655 | h8655
                                · linarith only [h8470, h8655, hlam]
                                · rcases p8637_3 (m.d 2 4) (by simp) with h8657 | h8657
                                  · linarith only [h8474, h8657, hlam]
                                  · rcases p8637_3 (m.d 3 4) (by simp) with h8659 | h8659
                                    · rcases p8637_3 (m.d 4 5) (by simp) with h8660 | h8660
                                      · linarith only [h8480, h8660, hlam]
                                      · linarith only [h7593, h8660, hlam]
                                    · linarith only [h6799, h8659, hlam]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              rcases p8637_3 (m.d 0 4) (by simp) with h8664 | h8664
                              · linarith only [h6799, h8664, hlam]
                              · linarith only [h6794, h8664, hlam]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              rcases p8637_3 (m.d 0 4) (by simp) with h8667 | h8667
                              · linarith only [h6799, h8667, hlam]
                              · linarith only [h6797, h8667, hlam]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h6797, h7593, h8474, hc23, hc34, hlam, hphi, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h6793, h6799, h8467, h8480, hc23, hc34, hlam, hphi, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8468, h8474, h8480, hc23, hc34, hlam, hphi, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8474, h8480, hc23, hc34, hlam, hphi, p8637_1]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [h8480, hlam, p8637_0]
                            · have p8637_0 := h8637c.1
                              have p8637_1 := h8637c.2.1
                              have p8637_2 := h8637c.2.2.1
                              have p8637_3 := h8637c.2.2.2
                              linarith only [hlam, p8637_0]
                    · linarith only [h8469, h8630, hlam]
                  · linarith only [h8629, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h0, h6793, h6799, h7593, h8467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8481_1, p8606_1]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h0, h6793, h6799, h7593, h8467, hlam, p8481_1, p8606_2]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h0, h6794, h7593, h8468, hlam, p8481_1, p8606_2]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h0, h6795, h8469, hlam, p8481_1, p8606_2]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h6796, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h8467, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h8474, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h8476, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h6797, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h8468, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h6794, h7593, h8468, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8481_1, p8606_1, u0elo0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h8478, hlam, p8606_1]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h6798, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h8469, hlam, p8606_0]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h0, h6795, h8469, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8481_1, p8606_1, u0elo1]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [h0, h6795, h8469, hc24, hlam, hphi, ht0b, ht45, ht5b, p8481_1, p8606_1, u0elo1]
                · have p8606_0 := h8606c.1
                  have p8606_1 := h8606c.2.1
                  have p8606_2 := h8606c.2.2.1
                  have p8606_3 := h8606c.2.2.2
                  linarith only [hlam, p8606_0]
              · linarith only [h0, h6799, h7593, h8512, hlam, p8481_1, u0elo1]
              · linarith only [h0, h7593, h8512, hlam, p8481_1, u0elo1]
              · linarith only [h0, h8512, hlam, p8481_1, u0elo1]
      · linarith only [h6798, h8505, hlam]
    · linarith only [h6795, h8504, hlam]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6793, h8467, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8481_1, u0elo1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    rcases p8481_3 (m.d 0 1) (by simp) with h8706 | h8706
    · linarith only [h0, h8706, hlam]
    · linarith only [h6793, h8706, hlam]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    rcases p8481_3 (m.d 0 1) (by simp) with h8709 | h8709
    · linarith only [h0, h8709, hlam]
    · linarith only [h6794, h8709, hlam]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    rcases p8481_3 (m.d 0 1) (by simp) with h8712 | h8712
    · linarith only [h0, h8712, hlam]
    · linarith only [h6795, h8712, hlam]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6793, hlam, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6796, hlam, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6799, hlam, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h7373, hlam, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6794, hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6797, hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6793, h7593, h8467, h8480, hc23, hc34, hlam, hphi, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h7593, hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6795, hlam, p8481_0]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6798, hlam, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6793, h7593, h8467, h8480, hc23, hc34, hlam, hphi, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [h6794, h7593, h8467, h8470, h8480, hc23, hc34, hlam, hphi, p8481_1]
  · have p8481_0 := h8481c.1
    have p8481_1 := h8481c.2.1
    have p8481_2 := h8481c.2.2.1
    have p8481_3 := h8481c.2.2.2
    linarith only [hlam, p8481_0]

end R2N4
