import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_65S11

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_IR_L_I_L_R_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h331 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h524 | h524
  · rcases m.htr 0 2 4 (by decide) (by decide) with h525 | h525
    · rcases m.htr 0 2 5 (by decide) (by decide) with h526 | h526
      · rcases m.htr 0 3 4 (by decide) (by decide) with h527 | h527
        · rcases m.htr 0 3 5 (by decide) (by decide) with h528 | h528
          · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
            · rcases m.htr 1 2 4 (by decide) (by decide) with h530 | h530
              · rcases m.htr 1 2 5 (by decide) (by decide) with h531 | h531
                · rcases m.htr 1 3 5 (by decide) (by decide) with h532 | h532
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h533 | h533
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h534 | h534
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h535 | h535
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                          · linarith only [h524, h533, h536, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h2bigk with h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h0, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h0, h533, h535, h536, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h0, h535, h536, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              rcases p538_3 (m.d 0 2) (by simp) with h543 | h543
                              · rcases p538_3 (m.d 1 2) (by simp) with h544 | h544
                                · rcases p538_3 (m.d 2 3) (by simp) with h545 | h545
                                  · linarith only [h524, h545, hlam]
                                  · linarith only [h534, h545, hlam]
                                · linarith only [h531, h544, hlam]
                              · linarith only [h543, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h524, h533, h535, h536, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h533, h535, h536, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h535, h536, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              rcases p538_3 (m.d 0 2) (by simp) with h554 | h554
                              · linarith only [h0, h554, hlam]
                              · linarith only [h526, h554, hlam]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h524, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h529, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h524, h535, h536, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p538_1]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h0, h524, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p538_1, u2ehi4]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h525, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h530, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h533, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [hc24, hlam, hphi, p538_1, u2ehi4]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h526, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h531, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h534, hlam, p538_0]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [h535, hlam, p538_1]
                            · have p538_0 := h538c.1
                              have p538_1 := h538c.2.1
                              have p538_2 := h538c.2.2.1
                              have p538_3 := h538c.2.2.2
                              linarith only [hlam, p538_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h572 | h572
                          · linarith only [h0, h524, h533, h572, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases h2bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, h534, hc12, hlam, hphi, ht01, ht0b, ht5b, p574_1, u5ehi3]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h578 | h578
                              · rcases p574_3 (m.d 1 2) (by simp) with h579 | h579
                                · rcases p574_3 (m.d 2 3) (by simp) with h580 | h580
                                  · linarith only [h524, h580, hlam]
                                  · linarith only [h533, h580, hlam]
                                · linarith only [h530, h579, hlam]
                              · linarith only [h578, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h585 | h585
                              · rcases p574_3 (m.d 1 2) (by simp) with h586 | h586
                                · rcases p574_3 (m.d 2 3) (by simp) with h587 | h587
                                  · linarith only [h524, h587, hlam]
                                  · linarith only [h534, h587, hlam]
                                · linarith only [h531, h586, hlam]
                              · linarith only [h585, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h524, h534, hc12, hlam, hphi, ht01, ht0b, ht5b, p574_1, u5ehi3]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h534, hc12, hlam, hphi, ht01, ht0b, ht5b, p574_1, u5ehi3]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h595 | h595
                              · linarith only [h0, h595, hlam]
                              · linarith only [h525, h595, hlam]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h598 | h598
                              · linarith only [h0, h598, hlam]
                              · linarith only [h526, h598, hlam]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h524, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h529, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h524, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p574_1, u2ehi3]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, h524, h535, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p574_1, u2ehi3]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h525, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h530, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h533, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h535, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h526, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h531, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h534, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hc25, hlam, hphi, p574_1, u2ehi3]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h616 | h616
                        · linarith only [h0, h524, h528, h533, h534, h616, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h618 | h618
                          · linarith only [h0, h524, h528, h533, h534, h616, h618, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                          · rcases h2bigk with h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h0, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 2) (by simp) with h623 | h623
                              · rcases p620_3 (m.d 1 2) (by simp) with h624 | h624
                                · rcases p620_3 (m.d 2 3) (by simp) with h625 | h625
                                  · linarith only [h625, hlam, p620_0]
                                  · rcases p620_3 (m.d 2 4) (by simp) with h627 | h627
                                    · linarith only [h525, h627, hlam]
                                    · rcases p620_3 (m.d 2 5) (by simp) with h629 | h629
                                      · linarith only [h526, h629, hlam]
                                      · linarith only [h534, h629, hlam]
                                · linarith only [h529, h624, hlam]
                              · linarith only [h623, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 2) (by simp) with h634 | h634
                              · rcases p620_3 (m.d 1 2) (by simp) with h635 | h635
                                · rcases p620_3 (m.d 2 3) (by simp) with h636 | h636
                                  · linarith only [h524, h636, hlam]
                                  · linarith only [h533, h636, hlam]
                                · linarith only [h530, h635, hlam]
                              · linarith only [h634, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 2) (by simp) with h641 | h641
                              · rcases p620_3 (m.d 1 2) (by simp) with h642 | h642
                                · rcases p620_3 (m.d 2 3) (by simp) with h643 | h643
                                  · linarith only [h524, h643, hlam]
                                  · rcases p620_3 (m.d 2 4) (by simp) with h645 | h645
                                    · linarith only [h525, h645, hlam]
                                    · rcases p620_3 (m.d 2 5) (by simp) with h647 | h647
                                      · linarith only [h647, hlam, p620_0]
                                      · rcases h3bigk with h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c | h649c
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h331, hlam, p649_1]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          rcases p649_3 (m.d 0 3) (by simp) with h652 | h652
                                          · rcases p649_3 (m.d 1 3) (by simp) with h653 | h653
                                            · rcases p649_3 (m.d 2 3) (by simp) with h654 | h654
                                              · linarith only [h524, h654, hlam]
                                              · rcases p649_3 (m.d 3 4) (by simp) with h656 | h656
                                                · linarith only [h527, h656, hlam]
                                                · rcases p649_3 (m.d 3 5) (by simp) with h658 | h658
                                                  · linarith only [h528, h658, hlam]
                                                  · linarith only [h534, h658, hlam]
                                            · linarith only [h529, h653, hlam]
                                          · linarith only [h524, h652, hlam]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h528, h533, h534, hlam, p649_2]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h0, h524, h533, h534, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p649_1, u2ehi3]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h528, h529, h533, h534, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p649_1, u2ehi3]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          rcases p649_3 (m.d 0 3) (by simp) with h667 | h667
                                          · linarith only [h331, h667, hlam]
                                          · linarith only [h524, h667, hlam]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h331, h528, h533, h534, hlam, p649_2]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h533, h534, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p649_1, u2ehi3]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h524, hlam, p649_1]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h529, hlam, p649_1]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h528, h534, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p649_1]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h534, hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h527, hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h331, h528, h533, h534, hc34, hlam, hphi, ht23, p649_1, u2ehi3]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h533, hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h618, hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h528, hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h532, hlam, p649_0]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [h0, h524, h528, h533, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p649_1, u2ehi3]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          rcases p649_3 (m.d 0 3) (by simp) with h685 | h685
                                          · rcases p649_3 (m.d 1 3) (by simp) with h686 | h686
                                            · rcases p649_3 (m.d 2 3) (by simp) with h687 | h687
                                              · linarith only [h534, h687, hlam]
                                              · linarith only [h533, h687, hlam]
                                            · linarith only [h0, h331, h524, h528, h533, h686, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                          · linarith only [h527, h685, hlam]
                                        · have p649_0 := h649c.1
                                          have p649_1 := h649c.2.1
                                          have p649_2 := h649c.2.2.1
                                          have p649_3 := h649c.2.2.2
                                          linarith only [hlam, p649_0]
                                · linarith only [h531, h642, hlam]
                              · linarith only [h641, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h524, h533, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p620_1]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 2) (by simp) with h697 | h697
                              · linarith only [h0, h697, hlam]
                              · linarith only [h524, h697, hlam]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 2) (by simp) with h700 | h700
                              · linarith only [h0, h700, hlam]
                              · linarith only [h525, h700, hlam]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              rcases p620_3 (m.d 0 2) (by simp) with h703 | h703
                              · linarith only [h0, h703, hlam]
                              · linarith only [h526, h703, hlam]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h524, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h529, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h524, h528, h534, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p620_1, u2ehi3]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h534, hlam, p620_1]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h525, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h530, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h533, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h616, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h526, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h531, hlam, p620_0]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hc25, hlam, hphi, p620_1, u2ehi2]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [h0, h524, h528, h534, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p620_1, u2ehi3]
                            · have p620_0 := h620c.1
                              have p620_1 := h620c.2.1
                              have p620_2 := h620c.2.2.1
                              have p620_3 := h620c.2.2.2
                              linarith only [hlam, p620_0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h721 | h721
                      · linarith only [h0, h524, h527, h533, h721, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h723 | h723
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h724 | h724
                          · rcases h2bigk with h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h0, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              rcases p725_3 (m.d 0 2) (by simp) with h728 | h728
                              · rcases p725_3 (m.d 1 2) (by simp) with h729 | h729
                                · rcases p725_3 (m.d 2 3) (by simp) with h730 | h730
                                  · linarith only [h730, hlam, p725_0]
                                  · rcases p725_3 (m.d 2 4) (by simp) with h732 | h732
                                    · linarith only [h525, h732, hlam]
                                    · linarith only [h533, h732, hlam]
                                · linarith only [h529, h729, hlam]
                              · linarith only [h728, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h0, h723, hc12, hlam, hphi, ht01, ht0b, ht5b, p725_1, u5ehi4]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              rcases p725_3 (m.d 0 2) (by simp) with h738 | h738
                              · rcases p725_3 (m.d 1 2) (by simp) with h739 | h739
                                · rcases p725_3 (m.d 2 3) (by simp) with h740 | h740
                                  · linarith only [h524, h740, hlam]
                                  · rcases p725_3 (m.d 2 4) (by simp) with h742 | h742
                                    · linarith only [h525, h742, hlam]
                                    · linarith only [h723, h742, hlam]
                                · linarith only [h531, h739, hlam]
                              · linarith only [h738, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h524, h527, h721, h724, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p725_1]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              rcases p725_3 (m.d 0 2) (by simp) with h749 | h749
                              · linarith only [h0, h749, hlam]
                              · linarith only [h524, h749, hlam]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h723, hc12, hlam, hphi, ht01, ht0b, ht5b, p725_1, u5ehi4]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              rcases p725_3 (m.d 0 2) (by simp) with h753 | h753
                              · linarith only [h0, h753, hlam]
                              · linarith only [h526, h753, hlam]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h524, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h529, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h533, hlam, p725_1]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h721, hlam, p725_1]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h525, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h530, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [hc24, hlam, hphi, p725_1, u2ehi2]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h527, h533, h721, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p725_1, u2ehi2]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h526, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h531, hlam, p725_0]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [hc25, hlam, hphi, p725_1, u2ehi2]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [h723, hlam, p725_1]
                            · have p725_0 := h725c.1
                              have p725_1 := h725c.2.1
                              have p725_2 := h725c.2.2.1
                              have p725_3 := h725c.2.2.2
                              linarith only [hlam, p725_0]
                          · linarith only [h533, h724, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h772 | h772
                          · linarith only [h331, h527, h529, h723, h772, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h533, h772, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h331, h528, h532, hlam]
                · linarith only [h0, h524, h531, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h525, h530, hlam]
            · linarith only [h0, h524, h529, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h779 | h779
            · rcases m.htr 1 2 4 (by decide) (by decide) with h780 | h780
              · rcases m.htr 1 2 5 (by decide) (by decide) with h781 | h781
                · rcases m.htr 1 3 5 (by decide) (by decide) with h782 | h782
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h783 | h783
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h784 | h784
                      · linarith only [h524, h528, h784, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h786 | h786
                        · linarith only [h525, h527, h528, h779, h782, h786, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h788 | h788
                          · linarith only [h524, h528, h779, h782, h783, h786, h788, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases h2bigk with h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c | h790c
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h0, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              rcases p790_3 (m.d 0 2) (by simp) with h793 | h793
                              · rcases p790_3 (m.d 1 2) (by simp) with h794 | h794
                                · rcases p790_3 (m.d 2 3) (by simp) with h795 | h795
                                  · linarith only [h795, hlam, p790_0]
                                  · rcases p790_3 (m.d 2 4) (by simp) with h797 | h797
                                    · linarith only [h525, h797, hlam]
                                    · rcases p790_3 (m.d 2 5) (by simp) with h799 | h799
                                      · linarith only [h526, h799, hlam]
                                      · linarith only [h784, h799, hlam]
                                · linarith only [h779, h794, hlam]
                              · linarith only [h793, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              rcases p790_3 (m.d 0 2) (by simp) with h804 | h804
                              · rcases p790_3 (m.d 1 2) (by simp) with h805 | h805
                                · rcases p790_3 (m.d 2 3) (by simp) with h806 | h806
                                  · linarith only [h524, h806, hlam]
                                  · linarith only [h783, h806, hlam]
                                · linarith only [h780, h805, hlam]
                              · linarith only [h804, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              rcases p790_3 (m.d 0 2) (by simp) with h811 | h811
                              · rcases p790_3 (m.d 1 2) (by simp) with h812 | h812
                                · rcases p790_3 (m.d 2 3) (by simp) with h813 | h813
                                  · linarith only [h524, h813, hlam]
                                  · rcases p790_3 (m.d 2 4) (by simp) with h815 | h815
                                    · linarith only [h525, h815, hlam]
                                    · rcases p790_3 (m.d 2 5) (by simp) with h817 | h817
                                      · linarith only [h817, hlam, p790_0]
                                      · rcases h3bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h331, hlam, p819_1]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h528, h779, h782, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p819_1]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h528, h779, h782, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p819_1]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h528, hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          rcases p819_3 (m.d 0 3) (by simp) with h825 | h825
                                          · linarith only [h331, h825, hlam]
                                          · rcases p819_3 (m.d 1 3) (by simp) with h827 | h827
                                            · rcases p819_3 (m.d 2 3) (by simp) with h828 | h828
                                              · linarith only [h779, h828, hlam]
                                              · rcases p819_3 (m.d 3 4) (by simp) with h830 | h830
                                                · linarith only [h524, h528, h782, h783, h830, hc34, hlam, hphi, ht23, u2ehi3]
                                                · rcases p819_3 (m.d 3 5) (by simp) with h832 | h832
                                                  · linarith only [h782, h832, hlam]
                                                  · linarith only [h528, h832, hlam]
                                            · linarith only [h331, h827, hlam]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          rcases p819_3 (m.d 0 3) (by simp) with h837 | h837
                                          · linarith only [h331, h837, hlam]
                                          · linarith only [h524, h837, hlam]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h524, h528, h782, h783, hlam, p819_2]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h524, h528, h783, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p819_1, u2ehi3]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h524, hlam, p819_1]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h779, hlam, p819_1]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h524, h528, h788, hc34, hc45, hlam, hphi, p819_1]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h784, hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h527, hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h528, h782, hc03, hc34, hlam, hphi, p819_1]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h783, hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h788, hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h524, h782, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p819_1, u2ehi2]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h782, hlam, p819_0]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [h779, h782, h783, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p819_1, u2ehi3]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          rcases p819_3 (m.d 0 3) (by simp) with h855 | h855
                                          · linarith only [h528, h855, hlam]
                                          · linarith only [h527, h855, hlam]
                                        · have p819_0 := h819c.1
                                          have p819_1 := h819c.2.1
                                          have p819_2 := h819c.2.2.1
                                          have p819_3 := h819c.2.2.2
                                          linarith only [hlam, p819_0]
                                · linarith only [h781, h812, hlam]
                              · linarith only [h811, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h524, h783, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p790_1, u2ehi3]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              rcases p790_3 (m.d 0 2) (by simp) with h863 | h863
                              · linarith only [h0, h863, hlam]
                              · linarith only [h524, h863, hlam]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              rcases p790_3 (m.d 0 2) (by simp) with h866 | h866
                              · linarith only [h0, h866, hlam]
                              · linarith only [h525, h866, hlam]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              rcases p790_3 (m.d 0 2) (by simp) with h869 | h869
                              · linarith only [h0, h869, hlam]
                              · linarith only [h526, h869, hlam]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h524, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h779, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h526, h784, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p790_1, u2ehi3]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h784, hlam, p790_1]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h525, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h780, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h783, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h786, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h526, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h781, hlam, p790_0]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h526, h783, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p790_1]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [h526, h528, h779, h782, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p790_1, u2ehi3]
                            · have p790_0 := h790c.1
                              have p790_1 := h790c.2.1
                              have p790_2 := h790c.2.2.1
                              have p790_3 := h790c.2.2.2
                              linarith only [hlam, p790_0]
                    · linarith only [h527, h528, h779, h782, h783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h889 | h889
                      · linarith only [h331, h782, h889, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h891 | h891
                        · linarith only [h888, h889, h891, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h893 | h893
                          · linarith only [h891, h893, hc34, hlam, hphi, ht23, u2ehi3]
                          · rcases h2bigk with h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h0, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              rcases p895_3 (m.d 0 2) (by simp) with h898 | h898
                              · rcases p895_3 (m.d 1 2) (by simp) with h899 | h899
                                · rcases p895_3 (m.d 2 3) (by simp) with h900 | h900
                                  · linarith only [h900, hlam, p895_0]
                                  · rcases p895_3 (m.d 2 4) (by simp) with h902 | h902
                                    · linarith only [h525, h902, hlam]
                                    · rcases p895_3 (m.d 2 5) (by simp) with h904 | h904
                                      · linarith only [h526, h904, hlam]
                                      · linarith only [h889, h904, hlam]
                                · linarith only [h779, h899, hlam]
                              · linarith only [h898, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              rcases p895_3 (m.d 0 2) (by simp) with h909 | h909
                              · rcases p895_3 (m.d 1 2) (by simp) with h910 | h910
                                · rcases p895_3 (m.d 2 3) (by simp) with h911 | h911
                                  · linarith only [h524, h911, hlam]
                                  · linarith only [h888, h911, hlam]
                                · linarith only [h780, h910, hlam]
                              · linarith only [h909, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              rcases p895_3 (m.d 0 2) (by simp) with h916 | h916
                              · rcases p895_3 (m.d 1 2) (by simp) with h917 | h917
                                · rcases p895_3 (m.d 2 3) (by simp) with h918 | h918
                                  · linarith only [h524, h918, hlam]
                                  · rcases p895_3 (m.d 2 4) (by simp) with h920 | h920
                                    · linarith only [h525, h920, hlam]
                                    · rcases p895_3 (m.d 2 5) (by simp) with h922 | h922
                                      · linarith only [h922, hlam, p895_0]
                                      · rcases h3bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h331, hlam, p924_1]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h331, h782, h888, hc35, hlam, hphi, ht23, p924_1, u2ehi3]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h331, h782, h893, hc34, hc45, hlam, hphi, p924_1]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h528, hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h782, h893, hc03, hc45, hlam, hphi, ht34, p924_1]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h782, h888, h893, hc45, hlam, hphi, ht23, ht34, p924_1, u2ehi3]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h782, h893, hc34, hc45, hlam, hphi, p924_1]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h782, hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h524, hlam, p924_1]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h779, hlam, p924_1]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h0, h889, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p895_1, p924_1]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h889, hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h527, hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h0, h331, h888, h889, hc01, hc12, hc34, hlam, hphi, ht23, p895_1, p924_1, u2ehi3]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h888, hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h893, hlam, p924_0]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h524, h888, h893, hc45, hlam, hphi, ht23, ht34, p924_1, u2ehi3]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h0, h331, h888, h889, h893, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p895_1, p924_1, u2ehi3]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [h888, h893, hc45, hlam, hphi, ht23, ht34, p924_1, u2ehi3]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          rcases p924_3 (m.d 0 3) (by simp) with h948 | h948
                                          · linarith only [h528, h948, hlam]
                                          · linarith only [h527, h948, hlam]
                                        · have p924_0 := h924c.1
                                          have p924_1 := h924c.2.1
                                          have p924_2 := h924c.2.2.1
                                          have p924_3 := h924c.2.2.2
                                          linarith only [hlam, p924_0]
                                · linarith only [h781, h917, hlam]
                              · linarith only [h916, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h524, h888, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p895_1, u2ehi3]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              rcases p895_3 (m.d 0 2) (by simp) with h956 | h956
                              · linarith only [h0, h956, hlam]
                              · linarith only [h524, h956, hlam]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              rcases p895_3 (m.d 0 2) (by simp) with h959 | h959
                              · linarith only [h0, h959, hlam]
                              · linarith only [h525, h959, hlam]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              rcases p895_3 (m.d 0 2) (by simp) with h962 | h962
                              · linarith only [h0, h962, hlam]
                              · linarith only [h526, h962, hlam]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h524, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h779, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h526, h889, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p895_1, u2ehi3]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h889, hlam, p895_1]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h525, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h780, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h888, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h891, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h526, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h781, hlam, p895_0]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h526, h888, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p895_1]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [h0, h526, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p895_1, u2ehi3]
                            · have p895_0 := h895c.1
                              have p895_1 := h895c.2.1
                              have p895_2 := h895c.2.2.1
                              have p895_3 := h895c.2.2.2
                              linarith only [hlam, p895_0]
                    · linarith only [h527, h528, h888, hc23, hc35, hlam, hphi]
                · linarith only [h0, h526, h781, hlam]
              · linarith only [h0, h526, h780, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h526, h779, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h984 | h984
          · rcases m.htr 1 2 3 (by decide) (by decide) with h985 | h985
            · rcases m.htr 1 2 4 (by decide) (by decide) with h986 | h986
              · rcases m.htr 1 2 5 (by decide) (by decide) with h987 | h987
                · rcases m.htr 1 3 5 (by decide) (by decide) with h988 | h988
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
                    · linarith only [h524, h527, h984, h989, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h991 | h991
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h992 | h992
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h993 | h993
                          · rcases h2bigk with h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c | h994c
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h0, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h991, h993, hc02, hlam, hphi, ht0b, ht5b, p994_1, u5ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h0, h989, h991, h993, hc12, hlam, hphi, ht01, ht0b, ht5b, p994_1, u5ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              rcases p994_3 (m.d 0 2) (by simp) with h999 | h999
                              · rcases p994_3 (m.d 1 2) (by simp) with h1000 | h1000
                                · rcases p994_3 (m.d 2 3) (by simp) with h1001 | h1001
                                  · linarith only [h1001, h524, hlam]
                                  · linarith only [h1001, h991, hlam]
                                · linarith only [h1000, h987, hlam]
                              · linarith only [h999, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h524, h991, h993, hc12, hlam, hphi, ht01, ht0b, ht5b, p994_1, u5ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h991, h993, hc12, hlam, hphi, ht01, ht0b, ht5b, p994_1, u5ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h989, h991, h993, hc12, hlam, hphi, ht01, ht0b, ht5b, p994_1, u5ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              rcases p994_3 (m.d 0 2) (by simp) with h1010 | h1010
                              · linarith only [h0, h1010, hlam]
                              · linarith only [h1010, h526, hlam]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h524, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h985, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h989, hlam, p994_1]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h524, h527, hc34, hlam, hphi, ht23, p994_1, u2ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h525, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h986, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h525, h991, h993, hc02, hlam, hphi, ht0b, ht5b, p994_1, u5ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h0, h524, h525, h527, h991, h993, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht5b, p994_1, u2ehi4, u5ehi4]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h526, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h987, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h991, hlam, p994_0]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [h992, hlam, p994_1]
                            · have p994_0 := h994c.1
                              have p994_1 := h994c.2.1
                              have p994_2 := h994c.2.2.1
                              have p994_3 := h994c.2.2.2
                              linarith only [hlam, p994_0]
                          · linarith only [h524, h527, h991, h993, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · linarith only [h989, h991, h992, hlam]
                      · linarith only [h527, h984, h991, hc23, hc34, hlam, hphi]
                  · linarith only [h331, h984, h988, hlam]
                · linarith only [h0, h526, h527, h984, h987, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h0, h524, h986, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h524, h985, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1035 | h1035
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1036 | h1036
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1037 | h1037
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1038 | h1038
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
                    · linarith only [h1039, h524, h527, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1041 | h1041
                      · linarith only [h1041, h524, h984, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1043 | h1043
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1044 | h1044
                          · rcases h2bigk with h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h0, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              rcases p1045_3 (m.d 0 2) (by simp) with h1048 | h1048
                              · rcases p1045_3 (m.d 1 2) (by simp) with h1049 | h1049
                                · rcases p1045_3 (m.d 2 3) (by simp) with h1050 | h1050
                                  · linarith only [h1050, hlam, p1045_0]
                                  · rcases p1045_3 (m.d 2 4) (by simp) with h1052 | h1052
                                    · linarith only [h1052, h525, hlam]
                                    · linarith only [h1039, h1052, hlam]
                                · linarith only [h1035, h1049, hlam]
                              · linarith only [h1048, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1043, hc02, hlam, hphi, ht0b, ht5b, p1045_1, u5ehi4]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              rcases p1045_3 (m.d 0 2) (by simp) with h1058 | h1058
                              · rcases p1045_3 (m.d 1 2) (by simp) with h1059 | h1059
                                · rcases p1045_3 (m.d 2 3) (by simp) with h1060 | h1060
                                  · linarith only [h1060, h524, hlam]
                                  · rcases p1045_3 (m.d 2 4) (by simp) with h1062 | h1062
                                    · linarith only [h1062, h525, hlam]
                                    · linarith only [h1043, h1062, hlam]
                                · linarith only [h1037, h1059, hlam]
                              · linarith only [h1058, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h524, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1045_1, u2ehi2]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              rcases p1045_3 (m.d 0 2) (by simp) with h1069 | h1069
                              · linarith only [h0, h1069, hlam]
                              · linarith only [h1069, h524, hlam]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1043, hc12, hlam, hphi, ht01, ht0b, ht5b, p1045_1, u5ehi4]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              rcases p1045_3 (m.d 0 2) (by simp) with h1073 | h1073
                              · linarith only [h0, h1073, hlam]
                              · linarith only [h1073, h526, hlam]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h524, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1035, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1039, hlam, p1045_1]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1041, hlam, p1045_1]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h525, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1036, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h525, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1045_1, u2ehi2]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h0, h1041, h525, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1045_1, u2ehi2]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h526, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1037, hlam, p1045_0]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [hc25, hlam, hphi, p1045_1, u2ehi2]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [h1043, hlam, p1045_1]
                            · have p1045_0 := h1045c.1
                              have p1045_1 := h1045c.2.1
                              have p1045_2 := h1045c.2.2.1
                              have p1045_3 := h1045c.2.2.2
                              linarith only [hlam, p1045_0]
                          · linarith only [h1044, h524, h527, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h1043, h1092, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1092, h524, h527, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
                    · linarith only [h1095, h524, h527, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1097 | h1097
                      · linarith only [h1038, h1097, h524, h527, hc13, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1099 | h1099
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1100 | h1100
                          · rcases h2bigk with h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              rcases p1101_3 (m.d 0 2) (by simp) with h1104 | h1104
                              · rcases p1101_3 (m.d 1 2) (by simp) with h1105 | h1105
                                · rcases p1101_3 (m.d 2 3) (by simp) with h1106 | h1106
                                  · linarith only [h1106, hlam, p1101_0]
                                  · rcases p1101_3 (m.d 2 4) (by simp) with h1108 | h1108
                                    · linarith only [h1108, h525, hlam]
                                    · linarith only [h1095, h1108, hlam]
                                · linarith only [h1035, h1105, hlam]
                              · linarith only [h1104, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1099, hc12, hlam, hphi, ht01, ht0b, ht5b, p1101_1, u5ehi4]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              rcases p1101_3 (m.d 0 2) (by simp) with h1114 | h1114
                              · rcases p1101_3 (m.d 1 2) (by simp) with h1115 | h1115
                                · rcases p1101_3 (m.d 2 3) (by simp) with h1116 | h1116
                                  · linarith only [h1116, h524, hlam]
                                  · rcases p1101_3 (m.d 2 4) (by simp) with h1118 | h1118
                                    · linarith only [h1118, h525, hlam]
                                    · linarith only [h1099, h1118, hlam]
                                · linarith only [h1037, h1115, hlam]
                              · linarith only [h1114, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h524, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1101_1, u2ehi2]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              rcases p1101_3 (m.d 0 2) (by simp) with h1125 | h1125
                              · linarith only [h0, h1125, hlam]
                              · linarith only [h1125, h524, hlam]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1099, hc12, hlam, hphi, ht01, ht0b, ht5b, p1101_1, u5ehi4]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              rcases p1101_3 (m.d 0 2) (by simp) with h1129 | h1129
                              · linarith only [h0, h1129, hlam]
                              · linarith only [h1129, h526, hlam]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h524, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1035, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1095, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1097, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h525, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1036, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h525, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1101_1, u2ehi2]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1097, h525, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1101_1, u2ehi2]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h526, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1037, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hc25, hlam, hphi, p1101_1, u2ehi2]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1099, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                          · linarith only [h1100, h524, h527, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1148 | h1148
                          · linarith only [h1099, h1148, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1148, h524, h527, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h0, h1037, h524, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h1036, h525, hlam]
            · linarith only [h0, h1035, h524, hlam]
      · linarith only [h524, h526, hc25, hlam, hphi, u2ehi2]
    · linarith only [h524, h525, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1156 | h1156
    · linarith only [h1156, h524, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1158 | h1158
      · linarith only [h1158, h524, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1160 | h1160
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1161 | h1161
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1162 | h1162
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1163 | h1163
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1164 | h1164
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1165 | h1165
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1166 | h1166
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1167 | h1167
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1168 | h1168
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1169 | h1169
                          · linarith only [h1160, h1162, h1169, h524, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases h2bigk with h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h0, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h524, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1156, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1158, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              rcases p1171_3 (m.d 0 2) (by simp) with h1177 | h1177
                              · linarith only [h0, h1177, hlam]
                              · rcases p1171_3 (m.d 1 2) (by simp) with h1179 | h1179
                                · rcases p1171_3 (m.d 2 3) (by simp) with h1180 | h1180
                                  · linarith only [h1162, h1180, hlam]
                                  · linarith only [h1180, h524, hlam]
                                · linarith only [h0, h1179, hlam]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1158, h1166, h1168, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1158, h1168, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1158, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hc23, hlam, hphi, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1162, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1158, h1162, h1168, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1158, h1162, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hc24, hlam, hphi, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1163, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1166, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1158, h1162, h1166, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hc25, hlam, hphi, p1171_1, u2ehi0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1164, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1167, hlam, p1171_0]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [h1168, hlam, p1171_1]
                            · have p1171_0 := h1171c.1
                              have p1171_1 := h1171c.2.1
                              have p1171_2 := h1171c.2.2.1
                              have p1171_3 := h1171c.2.2.2
                              linarith only [hlam, p1171_0]
                        · linarith only [h1156, h1168, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1167, h524, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1166, h524, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1161, h1165, h331, hlam]
                · linarith only [h1162, h1164, hc25, hlam, hphi, u2ehi2]
              · linarith only [h1162, h1163, h524, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1209 | h1209
              · linarith only [h1162, h1209, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1211 | h1211
                · linarith only [h1162, h1211, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1213 | h1213
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1214 | h1214
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1215 | h1215
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1217 | h1217
                          · rcases h2bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h0, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h524, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1156, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1158, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1211, h1214, h1216, hc23, hlam, hphi, p1218_1, u2ehi0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1162, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1209, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1211, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hc23, hlam, hphi, p1218_1, u2ehi0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hc23, hlam, hphi, p1218_1, u2ehi1]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hc23, hlam, hphi, p1218_1, u2ehi3]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h0, h1211, hc01, hc23, hlam, hphi, ht12, p1218_1]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hc24, hlam, hphi, p1218_1, u2ehi0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1218_1]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1214, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h0, h1211, h1214, hc01, hc23, hlam, hphi, ht12, p1218_1]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hc25, hlam, hphi, p1218_1, u2ehi0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1218_1]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1215, hlam, p1218_0]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [h1216, hlam, p1218_1]
                            · have p1218_0 := h1218c.1
                              have p1218_1 := h1218c.2.1
                              have p1218_2 := h1218c.2.2.1
                              have p1218_3 := h1218c.2.2.2
                              linarith only [hlam, p1218_0]
                          · rcases h2bigk with h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h0, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h524, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1156, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1158, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1162, hc23, hlam, hphi, p1244_1, u2ehi0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1162, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1209, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1211, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc23, hlam, hphi, p1244_1, u2ehi0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc23, hlam, hphi, p1244_1, u2ehi1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1216, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1244_1, u5ehi4]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h0, h1211, hc01, hc23, hlam, hphi, ht12, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc24, hlam, hphi, p1244_1, u2ehi0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1214, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h0, h1211, h1214, hc01, hc23, hlam, hphi, ht12, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hc25, hlam, hphi, p1244_1, u2ehi0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1215, hlam, p1244_0]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [h1216, hlam, p1244_1]
                            · have p1244_0 := h1244c.1
                              have p1244_1 := h1244c.2.1
                              have p1244_2 := h1244c.2.2.1
                              have p1244_3 := h1244c.2.2.2
                              linarith only [hlam, p1244_0]
                        · linarith only [h1156, h1216, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1215, h524, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h1160, h1162, h1214, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h1161, h1213, h331, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1275 | h1275
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1276 | h1276
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1277 | h1277
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1279 | h1279
                      · linarith only [h1156, h1160, h1161, h1274, h1279, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1279, h524, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1160, h1278, h524, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h1274, h1277, h524, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1274, h1276, h524, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1274, h1275, h524, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1286 | h1286
              · linarith only [h1274, h1286, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1288 | h1288
                · linarith only [h1274, h1288, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1290 | h1290
                  · linarith only [h1161, h1274, h1290, h524, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1292 | h1292
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1293 | h1293
                      · linarith only [h1274, h1290, h1293, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h1293, h524, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h1160, h1274, h1292, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1297 | h1297
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1298 | h1298
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1299 | h1299
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1300 | h1300
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1301 | h1301
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1302 | h1302
                    · linarith only [h1160, h1297, h1298, h1302, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · linarith only [h1302, h524, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1297, h1301, h331, hlam]
                · linarith only [h1298, h1300, hc25, hlam, hphi, u2ehi2]
              · linarith only [h1298, h1299, h524, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1308 | h1308
              · linarith only [h1298, h1308, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1310 | h1310
                · linarith only [h1298, h1310, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1312 | h1312
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1313 | h1313
                    · linarith only [h1160, h1297, h1313, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h1298, h1313, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h1297, h1312, h331, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1317 | h1317
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1318 | h1318
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1319 | h1319
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1320 | h1320
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1321 | h1321
                    · linarith only [h1160, h1321, h524, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1321, h524, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1317, h1320, h524, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1318, h1319, hc25, hlam, hphi, u2ehi3]
              · linarith only [h1317, h1318, h524, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1327 | h1327
              · linarith only [h1317, h1327, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1329 | h1329
                · linarith only [h1317, h1329, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1331 | h1331
                  · linarith only [h1297, h1317, h1331, h524, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1333 | h1333
                    · linarith only [h1160, h1333, h524, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1333, h524, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_22_13_15_M_IR_L_I_L_R_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h331 | h331
  · exact r1l7_22_13_15_M_IR_L_I_L_R_x1_x0 m hb2 hb3 hb5 h0 h331
  · exact r1l7_22_13_15_M_IR_L_I_L_R_x1_x1 m hb2 hb3 hb5 h0 h331

end R2N4
