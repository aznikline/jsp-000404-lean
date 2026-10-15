import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S4
import Jsp000404.R1LeavesN7_28S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4215 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 0 4 5 (by decide) (by decide) with h4593 | h4593
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4594 | h4594
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4595 | h4595
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4596 | h4596
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4597 | h4597
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4598 | h4598
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4599 | h4599
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4600 | h4600
                · linarith only [h1965, h1968, h4600, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4602 | h4602
                  · linarith only [h1965, h4215, h4602, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4604 | h4604
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4605 | h4605
                      · rcases h0bigk with h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h0, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1414, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1414, h4215, h4593, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1728, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          rcases p4606_3 (m.d 0 1) (by simp) with h4612 | h4612
                          · linarith only [h0, h4612, hlam]
                          · rcases p4606_3 (m.d 0 2) (by simp) with h4614 | h4614
                            · rcases p4606_3 (m.d 0 3) (by simp) with h4615 | h4615
                              · linarith only [h1965, h4615, hlam]
                              · linarith only [h1414, h4615, hlam]
                            · linarith only [h0, h4614, hlam]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          rcases p4606_3 (m.d 0 1) (by simp) with h4620 | h4620
                          · linarith only [h0, h4620, hlam]
                          · rcases p4606_3 (m.d 0 2) (by simp) with h4622 | h4622
                            · rcases p4606_3 (m.d 0 3) (by simp) with h4623 | h4623
                              · linarith only [h1965, h4623, hlam]
                              · rcases p4606_3 (m.d 0 4) (by simp) with h4625 | h4625
                                · linarith only [h1966, h4625, hlam]
                                · linarith only [h1968, h4625, hlam]
                            · linarith only [h1965, h4622, hlam]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          rcases p4606_3 (m.d 0 1) (by simp) with h4629 | h4629
                          · linarith only [h0, h4629, hlam]
                          · rcases p4606_3 (m.d 0 2) (by simp) with h4631 | h4631
                            · rcases p4606_3 (m.d 0 3) (by simp) with h4632 | h4632
                              · linarith only [h1965, h4632, hlam]
                              · rcases p4606_3 (m.d 0 4) (by simp) with h4634 | h4634
                                · linarith only [h1966, h4634, hlam]
                                · rcases p4606_3 (m.d 0 5) (by simp) with h4636 | h4636
                                  · linarith only [h1967, h4636, hlam]
                                  · rcases h0emax with h4638 | h4638 | h4638 | h4638 | h4638
                                    · rcases h5bigk with h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h1728, hlam, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h0, h4593, h4602, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4606_1, p4639_1, u2ehi2]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4215, hlam, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4606_1, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h1414, h4215, hc01, hc15, hlam, hphi, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4596, h4602, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4639_1, u2ehi2]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h1965, h4215, h4598, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4639_1, u2ehi2]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        rcases p4639_3 (m.d 0 5) (by simp) with h4649 | h4649
                                        · linarith only [h1728, h4649, hlam]
                                        · linarith only [h4593, h4649, hlam]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h1967, hlam, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4596, hlam, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4602, hlam, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h0, h1966, h4604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h1967, h4605, hc34, hlam, hphi, ht23, p4639_1, u2ehi4]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4598, hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4594, h4597, h4605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4639_1, u2ehi4]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4594, h4597, h4605, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4639_1]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4593, hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4599, hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4604, hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [h4605, hlam, p4639_0]
                                      · have p4639_0 := h4639c.1
                                        have p4639_1 := h4639c.2.1
                                        have p4639_2 := h4639c.2.2.1
                                        have p4639_3 := h4639c.2.2.2
                                        linarith only [hlam, p4639_0]
                                    · linarith only [h4215, h4593, h4638, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p4606_1]
                                    · rcases h5bigk with h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h1728, hlam, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4593, h4602, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4606_1, p4668_1, u2ehi2]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4215, hlam, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4606_1, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h1728, h4594, h4597, h4599, hc01, hc12, hlam, hphi, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4594, h4597, h4599, h4602, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4668_1, u2ehi2]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h1965, h4215, h4594, h4597, h4599, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4668_1, u2ehi2]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        rcases p4668_3 (m.d 0 5) (by simp) with h4678 | h4678
                                        · linarith only [h1728, h4678, hlam]
                                        · linarith only [h4593, h4678, hlam]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h1967, hlam, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4596, hlam, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4602, hlam, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h0, h1966, h4604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h1967, hc35, hlam, hphi, ht23, p4668_1, u2ehi4]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4598, hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4594, h4598, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4668_1, u2ehi4]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4594, h4597, h4605, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4668_1]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4593, hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4599, hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4604, hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [h4605, hlam, p4668_0]
                                      · have p4668_0 := h4668c.1
                                        have p4668_1 := h4668c.2.1
                                        have p4668_2 := h4668c.2.2.1
                                        have p4668_3 := h4668c.2.2.2
                                        linarith only [hlam, p4668_0]
                                    · rcases h5bigk with h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c | h4696c
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h1728, hlam, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4602, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4696_1, u2ehi2]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4215, hlam, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4606_1, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h1728, h4594, h4597, h4599, hc01, hc12, hlam, hphi, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4594, h4597, h4599, h4602, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4696_1, u2ehi2]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h1965, h4215, h4594, h4597, h4599, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4696_1, u2ehi2]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        rcases p4696_3 (m.d 0 5) (by simp) with h4706 | h4706
                                        · linarith only [h1728, h4706, hlam]
                                        · linarith only [h4593, h4706, hlam]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h1967, hlam, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4596, hlam, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4602, hlam, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h0, h1967, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h1967, hc35, hlam, hphi, ht23, p4696_1, u2ehi4]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4598, hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4594, h4598, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4696_1, u2ehi4]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4594, h4597, h4605, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4696_1]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4593, hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4599, hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4604, hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [h4605, hlam, p4696_0]
                                      · have p4696_0 := h4696c.1
                                        have p4696_1 := h4696c.2.1
                                        have p4696_2 := h4696c.2.2.1
                                        have p4696_3 := h4696c.2.2.2
                                        linarith only [hlam, p4696_0]
                                    · rcases h5bigk with h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h1728, hlam, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4602, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4724_1, u2ehi2]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4215, hlam, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4606_1, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h1728, h4594, h4597, h4599, hc01, hc12, hlam, hphi, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4594, h4597, h4599, h4602, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4724_1, u2ehi2]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h1965, h4215, h4594, h4597, h4599, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4724_1, u2ehi2]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        rcases p4724_3 (m.d 0 5) (by simp) with h4734 | h4734
                                        · linarith only [h1728, h4734, hlam]
                                        · linarith only [h4593, h4734, hlam]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h1967, hlam, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4596, hlam, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4602, hlam, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h0, h1967, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h1967, hc35, hlam, hphi, ht23, p4724_1, u2ehi4]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4598, hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4594, h4598, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4724_1, u2ehi4]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4594, h4597, h4605, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4724_1]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4593, hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4599, hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4604, hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [h4605, hlam, p4724_0]
                                      · have p4724_0 := h4724c.1
                                        have p4724_1 := h4724c.2.1
                                        have p4724_2 := h4724c.2.2.1
                                        have p4724_3 := h4724c.2.2.2
                                        linarith only [hlam, p4724_0]
                            · linarith only [h1966, h4631, hlam]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          rcases p4606_3 (m.d 0 1) (by simp) with h4753 | h4753
                          · linarith only [h0, h4753, hlam]
                          · rcases p4606_3 (m.d 0 2) (by simp) with h4755 | h4755
                            · rcases p4606_3 (m.d 0 3) (by simp) with h4756 | h4756
                              · linarith only [h1965, h4756, hlam]
                              · rcases p4606_3 (m.d 0 4) (by simp) with h4758 | h4758
                                · linarith only [h1966, h4758, hlam]
                                · linarith only [h4593, h4758, hlam]
                            · linarith only [h1967, h4755, hlam]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1968, h4594, h4597, hc01, hc12, hlam, hphi, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1965, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1968, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4215, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1968, h4594, h4597, hc01, hc12, hlam, hphi, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1966, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1414, h1968, h4594, h4597, hc01, hc12, hlam, hphi, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1965, h1968, h4215, h4594, h4597, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4606_1, u2ehi2]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4215, h4594, h4597, h4605, hc01, hc12, hlam, hphi, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1967, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h1965, h4215, h4594, h4597, h4605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4606_1, u2ehi2]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4593, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                      · linarith only [h1965, h1968, h4605, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h1968, h4593, h4604, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h1968, h4593, h4594, h4595, h4597, h4599, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h1966, h1968, h4597, h4598, hc35, hlam, hphi, ht23, u2ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4781 | h4781
            · linarith only [h1965, h4215, h4597, h4781, hc34, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4783 | h4783
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4784 | h4784
                · linarith only [h1414, h1965, h4597, h4784, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4786 | h4786
                  · linarith only [h1414, h4781, h4784, h4786, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4788 | h4788
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4789 | h4789
                      · rcases h0bigk with h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c | h4790c
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [hlam, p4790_0]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h0, hlam, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1414, hlam, p4790_0]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1414, h1965, h4215, h4593, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4790_1, u2ehi2]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1728, hlam, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          rcases p4790_3 (m.d 0 1) (by simp) with h4796 | h4796
                          · linarith only [h0, h4796, hlam]
                          · rcases p4790_3 (m.d 0 2) (by simp) with h4798 | h4798
                            · rcases p4790_3 (m.d 0 3) (by simp) with h4799 | h4799
                              · linarith only [h1965, h4799, hlam]
                              · linarith only [h1414, h4799, hlam]
                            · linarith only [h0, h4798, hlam]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [hlam, p4790_0]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          rcases p4790_3 (m.d 0 1) (by simp) with h4804 | h4804
                          · linarith only [h0, h4804, hlam]
                          · rcases p4790_3 (m.d 0 2) (by simp) with h4806 | h4806
                            · rcases p4790_3 (m.d 0 3) (by simp) with h4807 | h4807
                              · linarith only [h1965, h4807, hlam]
                              · rcases p4790_3 (m.d 0 4) (by simp) with h4809 | h4809
                                · linarith only [h1966, h4809, hlam]
                                · linarith only [h1968, h4809, hlam]
                            · linarith only [h1965, h4806, hlam]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          rcases p4790_3 (m.d 0 1) (by simp) with h4813 | h4813
                          · linarith only [h0, h4813, hlam]
                          · rcases p4790_3 (m.d 0 2) (by simp) with h4815 | h4815
                            · rcases p4790_3 (m.d 0 3) (by simp) with h4816 | h4816
                              · linarith only [h1965, h4816, hlam]
                              · rcases p4790_3 (m.d 0 4) (by simp) with h4818 | h4818
                                · linarith only [h1966, h4818, hlam]
                                · rcases p4790_3 (m.d 0 5) (by simp) with h4820 | h4820
                                  · linarith only [h1967, h4820, hlam]
                                  · rcases h0emax with h4822 | h4822 | h4822 | h4822 | h4822
                                    · rcases h5bigk with h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h1728, hlam, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4593, h4786, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4823_1, u2ehi2]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4215, hlam, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4790_1, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h1728, h4781, h4789, hc01, hc34, hlam, hphi, ht12, ht23, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4781, h4786, h4789, hc34, hlam, hphi, ht23, p4823_1, u2ehi2]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4781, hlam, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        rcases p4823_3 (m.d 0 5) (by simp) with h4833 | h4833
                                        · linarith only [h1728, h4833, hlam]
                                        · linarith only [h4593, h4833, hlam]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h1967, hlam, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4596, hlam, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4786, hlam, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h0, h1967, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4790_1, p4823_1]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h1967, h4786, h4789, hc34, hlam, hphi, ht23, p4823_1, u2ehi2]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h0, h1728, h1967, h4593, h4786, h4789, hc01, hc12, hc34, hlam, hphi, ht23, p4790_1, p4823_1, u2ehi2]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4786, h4789, hc34, hlam, hphi, ht23, p4823_1, u2ehi2]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        rcases p4823_3 (m.d 0 5) (by simp) with h4845 | h4845
                                        · linarith only [h4215, h4845, hlam]
                                        · linarith only [h4593, h4845, hlam]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4593, hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4783, hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4788, hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [h4789, hlam, p4823_0]
                                      · have p4823_0 := h4823c.1
                                        have p4823_1 := h4823c.2.1
                                        have p4823_2 := h4823c.2.2.1
                                        have p4823_3 := h4823c.2.2.2
                                        linarith only [hlam, p4823_0]
                                    · linarith only [h1967, h4593, h4786, h4822, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4790_1, u2ehi2]
                                    · rcases h5bigk with h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h1728, hlam, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h0, h4593, h4786, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4790_1, p4854_1, u2ehi2]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4215, hlam, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4790_1, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4596, h4786, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4854_1, u2ehi2]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4781, hlam, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        rcases p4854_3 (m.d 0 5) (by simp) with h4864 | h4864
                                        · linarith only [h1728, h4864, hlam]
                                        · linarith only [h4593, h4864, hlam]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h1967, hlam, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4596, hlam, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4786, hlam, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h0, h1966, h4788, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h1967, h4789, hc34, hlam, hphi, ht23, p4854_1, u2ehi4]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h1728, h4789, hc01, hc34, hlam, hphi, ht12, ht23, p4854_1]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4789, hc34, hlam, hphi, ht23, p4854_1, u2ehi4]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        rcases p4854_3 (m.d 0 5) (by simp) with h4876 | h4876
                                        · linarith only [h4215, h4876, hlam]
                                        · linarith only [h4593, h4876, hlam]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4593, hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4783, hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4788, hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [h4789, hlam, p4854_0]
                                      · have p4854_0 := h4854c.1
                                        have p4854_1 := h4854c.2.1
                                        have p4854_2 := h4854c.2.2.1
                                        have p4854_3 := h4854c.2.2.2
                                        linarith only [hlam, p4854_0]
                                    · rcases h5bigk with h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c | h4884c
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h1728, hlam, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h0, h4593, h4786, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4790_1, p4884_1, u2ehi2]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4215, hlam, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4790_1, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h1414, h4215, hc01, hc15, hlam, hphi, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4596, h4786, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4884_1, u2ehi2]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4781, hlam, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        rcases p4884_3 (m.d 0 5) (by simp) with h4894 | h4894
                                        · linarith only [h1728, h4894, hlam]
                                        · linarith only [h4593, h4894, hlam]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h1967, hlam, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4596, hlam, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4786, hlam, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h0, h1966, h4788, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4884_1]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h1967, h4789, hc34, hlam, hphi, ht23, p4884_1, u2ehi4]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h0, h1728, h1966, h4789, hc01, hc12, hc34, hlam, hphi, ht23, p4790_1, p4884_1, u2ehi3]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4789, hc34, hlam, hphi, ht23, p4884_1, u2ehi4]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        rcases p4884_3 (m.d 0 5) (by simp) with h4906 | h4906
                                        · linarith only [h4215, h4906, hlam]
                                        · linarith only [h4593, h4906, hlam]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4593, hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4783, hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4788, hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [h4789, hlam, p4884_0]
                                      · have p4884_0 := h4884c.1
                                        have p4884_1 := h4884c.2.1
                                        have p4884_2 := h4884c.2.2.1
                                        have p4884_3 := h4884c.2.2.2
                                        linarith only [hlam, p4884_0]
                                    · rcases h5bigk with h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c | h4914c
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h1728, hlam, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h0, h4593, h4786, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4790_1, p4914_1, u2ehi2]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4215, hlam, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h0, h4593, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4790_1, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h1414, h4215, hc01, hc15, hlam, hphi, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4596, h4786, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4914_1, u2ehi2]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4781, hlam, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        rcases p4914_3 (m.d 0 5) (by simp) with h4924 | h4924
                                        · linarith only [h1728, h4924, hlam]
                                        · linarith only [h4593, h4924, hlam]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h1967, hlam, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4596, hlam, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4786, hlam, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h0, h1966, h4788, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4914_1]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h1965, h4215, h4789, hc34, hlam, hphi, ht23, p4914_1, u2ehi2]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h0, h1728, h1966, h4789, hc01, hc12, hc34, hlam, hphi, ht23, p4790_1, p4914_1, u2ehi3]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4789, hc34, hlam, hphi, ht23, p4914_1, u2ehi4]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        rcases p4914_3 (m.d 0 5) (by simp) with h4936 | h4936
                                        · linarith only [h4215, h4936, hlam]
                                        · linarith only [h4593, h4936, hlam]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4593, hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4783, hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4788, hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [h4789, hlam, p4914_0]
                                      · have p4914_0 := h4914c.1
                                        have p4914_1 := h4914c.2.1
                                        have p4914_2 := h4914c.2.2.1
                                        have p4914_3 := h4914c.2.2.2
                                        linarith only [hlam, p4914_0]
                            · linarith only [h1966, h4815, hlam]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          rcases p4790_3 (m.d 0 1) (by simp) with h4945 | h4945
                          · linarith only [h0, h4945, hlam]
                          · rcases p4790_3 (m.d 0 2) (by simp) with h4947 | h4947
                            · rcases p4790_3 (m.d 0 3) (by simp) with h4948 | h4948
                              · linarith only [h1965, h4948, hlam]
                              · rcases p4790_3 (m.d 0 4) (by simp) with h4950 | h4950
                                · linarith only [h1966, h4950, hlam]
                                · linarith only [h4593, h4950, hlam]
                            · linarith only [h1967, h4947, hlam]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1968, hc01, hc34, hlam, hphi, ht12, ht23, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1965, hlam, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [hlam, p4790_0]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1968, hlam, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h4215, hlam, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          rcases p4790_3 (m.d 0 1) (by simp) with h4959 | h4959
                          · linarith only [h4959, hlam, p4790_0]
                          · rcases p4790_3 (m.d 0 2) (by simp) with h4961 | h4961
                            · rcases p4790_3 (m.d 0 3) (by simp) with h4962 | h4962
                              · linarith only [h1968, h4962, hlam]
                              · linarith only [h1414, h4962, hlam]
                            · linarith only [h0, h4961, hlam]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1966, hlam, p4790_0]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1965, h1968, hc34, hlam, hphi, ht23, p4790_1, u2ehi2]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [hlam, p4790_0]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1967, h1968, hc34, hlam, hphi, ht23, p4790_1, u2ehi4]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          rcases p4790_3 (m.d 0 1) (by simp) with h4970 | h4970
                          · linarith only [h1728, h4970, hlam]
                          · rcases p4790_3 (m.d 0 2) (by simp) with h4972 | h4972
                            · rcases p4790_3 (m.d 0 3) (by simp) with h4973 | h4973
                              · linarith only [h4215, h4973, hlam]
                              · linarith only [h1414, h4973, hlam]
                            · linarith only [h0, h4972, hlam]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1967, hlam, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h1965, h4215, h4789, hc34, hlam, hphi, ht23, p4790_1, u2ehi2]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [h4593, hlam, p4790_1]
                        · have p4790_0 := h4790c.1
                          have p4790_1 := h4790c.2.1
                          have p4790_2 := h4790c.2.2.1
                          have p4790_3 := h4790c.2.2.2
                          linarith only [hlam, p4790_0]
                      · linarith only [h1965, h1968, h4789, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h1968, h4593, h4784, h4788, hc34, hlam, hphi, ht23, u2ehi2]
              · linarith only [h1968, h4593, h4595, h4783, hc34, hlam, hphi, ht23, u2ehi3]
        · linarith only [h0, h1965, h4596, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1965, h4595, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1965, h4594, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4987 | h4987
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4988 | h4988
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4989 | h4989
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4990 | h4990
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4991 | h4991
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4992 | h4992
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4993 | h4993
                · linarith only [h1965, h1968, h4993, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4995 | h4995
                  · linarith only [h1965, h4215, h4995, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4997 | h4997
                    · linarith only [h1965, h1966, h1968, h4593, h4997, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4999 | h4999
                      · linarith only [h1965, h1968, h4593, h4999, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h1965, h1968, h4987, h4990, h4992, h4999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h1965, h1968, h4990, h4992, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h1965, h1968, h4990, h4991, hc35, hlam, hphi, ht23, u2ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5004 | h5004
            · linarith only [h1965, h4215, h4990, h5004, hc34, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5006 | h5006
              · linarith only [h1965, h1968, h4593, h4990, h5006, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5008 | h5008
                · linarith only [h1965, h1968, h5008, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5010 | h5010
                  · linarith only [h1965, h4215, h5010, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5012 | h5012
                    · linarith only [h1414, h4990, h5006, h5012, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5014 | h5014
                      · linarith only [h1966, h4593, h5014, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h1965, h1968, h5014, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h0, h1967, h4989, hlam]
      · linarith only [h0, h1967, h4988, hc24, hlam, hphi, u2ehi4]
    · linarith only [h0, h1967, h4987, hc23, hlam, hphi, u2ehi4]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 0 3 5 (by decide) (by decide) with h4215 | h4215
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x1_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h4215
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x1_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h4215

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 0 3 4 (by decide) (by decide) with h1968 | h1968
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  rcases m.htr 0 2 5 (by decide) (by decide) with h1967 | h1967
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5 m hb0 hb2 hb5 h0 h1414 h1728 h1965 h1966 h1967
  · linarith only [h1965, h1967, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 6112000 in
set_option maxHeartbeats 6112000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  rcases m.htr 0 2 4 (by decide) (by decide) with h1966 | h1966
  · exact r1l7_10_12_25_L_I_L_R_H_I_s4 m hb0 hb2 hb5 h0 h1414 h1728 h1965 h1966
  · linarith only [h1965, h1966, hc24, hlam, hphi, u2ehi2]

end R2N4
