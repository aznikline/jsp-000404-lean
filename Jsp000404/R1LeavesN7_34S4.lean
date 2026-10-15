import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S0
import Jsp000404.R1LeavesN7_34S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2081 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 3 5 (by decide) (by decide) with h3675 | h3675
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3676 | h3676
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3677 | h3677
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3678 | h3678
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3679 | h3679
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3680 | h3680
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3681 | h3681
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3682 | h3682
                · linarith only [h2078, h2081, h3682, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3684 | h3684
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3685 | h3685
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3686 | h3686
                      · rcases h0bigk with h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c | h3687c
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [hlam, p3687_0]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h0, hlam, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h1265, hlam, p3687_0]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h0, h2080, h2081, h3675, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3687_1, u2ehi4]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h1561, hlam, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          rcases p3687_3 (m.d 0 1) (by simp) with h3693 | h3693
                          · linarith only [h0, h3693, hlam]
                          · rcases p3687_3 (m.d 0 2) (by simp) with h3695 | h3695
                            · rcases p3687_3 (m.d 0 3) (by simp) with h3696 | h3696
                              · linarith only [h2078, h3696, hlam]
                              · linarith only [h1265, h3696, hlam]
                            · linarith only [h0, h3695, hlam]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [hlam, p3687_0]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          rcases p3687_3 (m.d 0 1) (by simp) with h3701 | h3701
                          · linarith only [h0, h3701, hlam]
                          · rcases p3687_3 (m.d 0 2) (by simp) with h3703 | h3703
                            · rcases p3687_3 (m.d 0 3) (by simp) with h3704 | h3704
                              · linarith only [h2078, h3704, hlam]
                              · rcases p3687_3 (m.d 0 4) (by simp) with h3706 | h3706
                                · linarith only [h2079, h3706, hlam]
                                · linarith only [h2081, h3706, hlam]
                            · linarith only [h2078, h3703, hlam]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          rcases p3687_3 (m.d 0 1) (by simp) with h3710 | h3710
                          · linarith only [h0, h3710, hlam]
                          · rcases p3687_3 (m.d 0 2) (by simp) with h3712 | h3712
                            · rcases p3687_3 (m.d 0 3) (by simp) with h3713 | h3713
                              · linarith only [h2078, h3713, hlam]
                              · rcases p3687_3 (m.d 0 4) (by simp) with h3715 | h3715
                                · linarith only [h2079, h3715, hlam]
                                · rcases p3687_3 (m.d 0 5) (by simp) with h3717 | h3717
                                  · linarith only [h2080, h3717, hlam]
                                  · rcases h3bigk with h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c | h3719c
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h1265, hlam, p3719_1]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h0, h2081, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3687_1, p3719_1]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h2081, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h0, h2081, h3686, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3687_1, p3719_1]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h2080, h3675, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3719_1, u2ehi4]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3677, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3719_1, u2ehi2]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h2080, h2081, h3675, h3677, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3719_1, u2ehi4]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      rcases p3719_3 (m.d 0 3) (by simp) with h3729 | h3729
                                      · linarith only [h1265, h3729, hlam]
                                      · linarith only [h3675, h3729, hlam]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h2078, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3677, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3682, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h0, h2078, h3686, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3719_1]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h2080, h3675, hc34, hlam, hphi, ht23, p3719_1, u2ehi4]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3679, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3677, h3679, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3719_1]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3677, h3679, h3686, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3719_1]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3675, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3680, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3684, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [h3686, hlam, p3719_0]
                                    · have p3719_0 := h3719c.1
                                      have p3719_1 := h3719c.2.1
                                      have p3719_2 := h3719c.2.2.1
                                      have p3719_3 := h3719c.2.2.2
                                      linarith only [hlam, p3719_0]
                            · linarith only [h2079, h3712, hlam]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          rcases p3687_3 (m.d 0 1) (by simp) with h3748 | h3748
                          · linarith only [h0, h3748, hlam]
                          · rcases p3687_3 (m.d 0 2) (by simp) with h3750 | h3750
                            · rcases p3687_3 (m.d 0 3) (by simp) with h3751 | h3751
                              · linarith only [h2078, h3751, hlam]
                              · linarith only [h3675, h3751, hlam]
                            · linarith only [h2080, h3750, hlam]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2081, h3677, h3679, hc01, hc12, hlam, hphi, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2078, hlam, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [hlam, p3687_0]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2081, hlam, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2080, h2081, h3677, h3679, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3687_1, u2ehi4]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2081, h3677, h3679, hc01, hc12, hlam, hphi, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2079, hlam, p3687_0]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h1265, h2081, h3677, h3679, hc01, hc12, hlam, hphi, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [hlam, p3687_0]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2080, h2081, h3677, h3679, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3687_1, u2ehi4]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2081, h3675, h3677, h3679, hc01, hc12, hlam, hphi, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h2080, hlam, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h3675, hlam, p3687_0]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [h3676, hlam, p3687_1]
                        · have p3687_0 := h3687c.1
                          have p3687_1 := h3687c.2.1
                          have p3687_2 := h3687c.2.2.1
                          have p3687_3 := h3687c.2.2.2
                          linarith only [hlam, p3687_0]
                      · linarith only [h2078, h2081, h3684, h3686, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · linarith only [h2081, h3675, h3676, h3677, h3679, h3685, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h2081, h3675, h3677, h3679, h3684, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h2081, h3675, h3676, h3677, h3678, h3679, h3681, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h2081, h3675, h3679, h3680, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3775 | h3775
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3776 | h3776
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3777 | h3777
                · linarith only [h1561, h3679, h3775, h3777, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3779 | h3779
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3780 | h3780
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3781 | h3781
                      · rcases h0bigk with h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c | h3782c
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [hlam, p3782_0]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h0, hlam, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h1265, hlam, p3782_0]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h1561, h3679, h3775, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h1561, hlam, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          rcases p3782_3 (m.d 0 1) (by simp) with h3788 | h3788
                          · linarith only [h0, h3788, hlam]
                          · rcases p3782_3 (m.d 0 2) (by simp) with h3790 | h3790
                            · rcases p3782_3 (m.d 0 3) (by simp) with h3791 | h3791
                              · linarith only [h2078, h3791, hlam]
                              · linarith only [h1265, h3791, hlam]
                            · linarith only [h0, h3790, hlam]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [hlam, p3782_0]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          rcases p3782_3 (m.d 0 1) (by simp) with h3796 | h3796
                          · linarith only [h0, h3796, hlam]
                          · rcases p3782_3 (m.d 0 2) (by simp) with h3798 | h3798
                            · rcases p3782_3 (m.d 0 3) (by simp) with h3799 | h3799
                              · linarith only [h2078, h3799, hlam]
                              · rcases p3782_3 (m.d 0 4) (by simp) with h3801 | h3801
                                · linarith only [h2079, h3801, hlam]
                                · linarith only [h2081, h3801, hlam]
                            · linarith only [h2078, h3798, hlam]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          rcases p3782_3 (m.d 0 1) (by simp) with h3805 | h3805
                          · linarith only [h0, h3805, hlam]
                          · rcases p3782_3 (m.d 0 2) (by simp) with h3807 | h3807
                            · rcases p3782_3 (m.d 0 3) (by simp) with h3808 | h3808
                              · linarith only [h2078, h3808, hlam]
                              · rcases p3782_3 (m.d 0 4) (by simp) with h3810 | h3810
                                · linarith only [h2079, h3810, hlam]
                                · rcases p3782_3 (m.d 0 5) (by simp) with h3812 | h3812
                                  · linarith only [h2080, h3812, hlam]
                                  · rcases h3bigk with h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h1265, hlam, p3814_1]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h0, h2081, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3782_1, p3814_1]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h2081, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h0, h2081, h3781, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3782_1, p3814_1]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3679, hc03, hc34, hlam, hphi, p3814_1]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3679, hc34, hlam, hphi, ht23, p3814_1, u2ehi2]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3679, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h0, h2080, h2081, h3675, h3679, h3781, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p3782_1, p3814_1, u2ehi4]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h2078, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3677, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3777, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h0, h2078, h3781, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3814_1]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h2080, h3675, hc34, hlam, hphi, ht23, p3814_1, u2ehi4]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p3814_1]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p3814_1]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      rcases p3814_3 (m.d 0 3) (by simp) with h3834 | h3834
                                      · linarith only [h2081, h3834, hlam]
                                      · linarith only [h3675, h3834, hlam]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3675, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3775, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3779, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [h3781, hlam, p3814_0]
                                    · have p3814_0 := h3814c.1
                                      have p3814_1 := h3814c.2.1
                                      have p3814_2 := h3814c.2.2.1
                                      have p3814_3 := h3814c.2.2.2
                                      linarith only [hlam, p3814_0]
                            · linarith only [h2079, h3807, hlam]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          rcases p3782_3 (m.d 0 1) (by simp) with h3843 | h3843
                          · linarith only [h0, h3843, hlam]
                          · rcases p3782_3 (m.d 0 2) (by simp) with h3845 | h3845
                            · rcases p3782_3 (m.d 0 3) (by simp) with h3846 | h3846
                              · linarith only [h2078, h3846, hlam]
                              · linarith only [h3675, h3846, hlam]
                            · linarith only [h2080, h3845, hlam]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2081, hc01, hc34, hlam, hphi, ht12, ht23, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2078, hlam, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [hlam, p3782_0]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2081, hlam, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2080, h2081, hc34, hlam, hphi, ht23, p3782_1, u2ehi4]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          rcases p3782_3 (m.d 0 1) (by simp) with h3855 | h3855
                          · linarith only [h3855, hlam, p3782_0]
                          · rcases p3782_3 (m.d 0 2) (by simp) with h3857 | h3857
                            · rcases p3782_3 (m.d 0 3) (by simp) with h3858 | h3858
                              · linarith only [h2081, h3858, hlam]
                              · linarith only [h1265, h3858, hlam]
                            · linarith only [h0, h3857, hlam]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2079, hlam, p3782_0]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2078, h2081, hc34, hlam, hphi, ht23, p3782_1, u2ehi2]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [hlam, p3782_0]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2080, h2081, hc34, hlam, hphi, ht23, p3782_1, u2ehi4]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h1265, h3675, h3679, hc01, hc34, hlam, hphi, ht12, ht23, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h2080, hlam, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h3675, hlam, p3782_0]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [h3676, hlam, p3782_1]
                        · have p3782_0 := h3782c.1
                          have p3782_1 := h3782c.2.1
                          have p3782_2 := h3782c.2.2.1
                          have p3782_3 := h3782c.2.2.2
                          linarith only [hlam, p3782_0]
                      · linarith only [h1265, h3679, h3781, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1265, h3675, h3676, h3679, h3780, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h1265, h3675, h3679, h3779, hc23, hc34, hlam, hphi]
              · linarith only [h1265, h3675, h3676, h3678, h3679, h3776, hc34, hlam, hphi, ht23, u2ehi3]
            · linarith only [h1265, h3675, h3775, hlam]
        · linarith only [h0, h2078, h3678, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h2078, h3677, hlam]
    · linarith only [h2081, h3675, h3676, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3879 | h3879
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3880 | h3880
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3881 | h3881
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3882 | h3882
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3883 | h3883
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3884 | h3884
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3885 | h3885
                · linarith only [h2078, h2081, h3885, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3887 | h3887
                  · linarith only [h2078, h3675, h3887, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3889 | h3889
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3890 | h3890
                      · rcases h0bigk with h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h0, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h1265, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h0, h2078, h3675, h3879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3891_1, u2ehi2]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h1561, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          rcases p3891_3 (m.d 0 1) (by simp) with h3897 | h3897
                          · linarith only [h0, h3897, hlam]
                          · rcases p3891_3 (m.d 0 2) (by simp) with h3899 | h3899
                            · rcases p3891_3 (m.d 0 3) (by simp) with h3900 | h3900
                              · linarith only [h2078, h3900, hlam]
                              · linarith only [h1265, h3900, hlam]
                            · linarith only [h0, h3899, hlam]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          rcases p3891_3 (m.d 0 1) (by simp) with h3905 | h3905
                          · linarith only [h0, h3905, hlam]
                          · rcases p3891_3 (m.d 0 2) (by simp) with h3907 | h3907
                            · rcases p3891_3 (m.d 0 3) (by simp) with h3908 | h3908
                              · linarith only [h2078, h3908, hlam]
                              · rcases p3891_3 (m.d 0 4) (by simp) with h3910 | h3910
                                · linarith only [h2079, h3910, hlam]
                                · linarith only [h2081, h3910, hlam]
                            · linarith only [h2078, h3907, hlam]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          rcases p3891_3 (m.d 0 1) (by simp) with h3914 | h3914
                          · linarith only [h0, h3914, hlam]
                          · rcases p3891_3 (m.d 0 2) (by simp) with h3916 | h3916
                            · rcases p3891_3 (m.d 0 3) (by simp) with h3917 | h3917
                              · linarith only [h2078, h3917, hlam]
                              · rcases p3891_3 (m.d 0 4) (by simp) with h3919 | h3919
                                · linarith only [h2079, h3919, hlam]
                                · rcases p3891_3 (m.d 0 5) (by simp) with h3921 | h3921
                                  · linarith only [h2080, h3921, hlam]
                                  · rcases h3bigk with h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c | h3923c
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h1265, hlam, p3923_1]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h0, h3675, h3879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3891_1, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h2081, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3675, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h1265, hc01, hc13, hlam, hphi, p3923_1]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h2078, h3675, h3880, h3890, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h2078, h3675, h3880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h2078, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3880, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3885, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3887, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h2078, hc34, hlam, hphi, ht23, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3882, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3880, h3882, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h2078, h3675, h3880, h3882, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h2078, h3883, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3883, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3880, h3883, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3923_1, u2ehi2]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [h3890, hlam, p3923_0]
                                    · have p3923_0 := h3923c.1
                                      have p3923_1 := h3923c.2.1
                                      have p3923_2 := h3923c.2.2.1
                                      have p3923_3 := h3923c.2.2.2
                                      linarith only [hlam, p3923_0]
                            · linarith only [h2079, h3916, hlam]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          rcases p3891_3 (m.d 0 1) (by simp) with h3950 | h3950
                          · linarith only [h0, h3950, hlam]
                          · rcases p3891_3 (m.d 0 2) (by simp) with h3952 | h3952
                            · rcases p3891_3 (m.d 0 3) (by simp) with h3953 | h3953
                              · linarith only [h2078, h3953, hlam]
                              · rcases p3891_3 (m.d 0 4) (by simp) with h3955 | h3955
                                · linarith only [h2079, h3955, hlam]
                                · linarith only [h3879, h3955, hlam]
                            · linarith only [h2080, h3952, hlam]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2081, h3880, h3882, hc01, hc12, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2078, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2081, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3675, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2081, h3880, h3882, hc01, hc12, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2079, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h1265, h2081, h3880, h3882, hc01, hc12, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h1561, h2081, h3880, h3882, hc01, hc12, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3675, h3880, h3882, h3890, hc01, hc12, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2080, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2078, h3675, h3880, h3882, h3890, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3891_1, u2ehi2]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3879, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                      · linarith only [h2078, h2081, h3890, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h2081, h3879, h3880, h3882, h3889, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h2081, h3879, h3880, h3881, h3882, h3884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h2079, h2081, h3882, h3883, hc35, hlam, hphi, ht23, u2ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3978 | h3978
            · linarith only [h2078, h3675, h3882, h3978, hc34, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3980 | h3980
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3981 | h3981
                · linarith only [h1265, h2078, h3882, h3981, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3983 | h3983
                  · linarith only [h0, h1561, h2078, h3978, h3983, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3985 | h3985
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3986 | h3986
                      · rcases h0bigk with h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c | h3987c
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [hlam, p3987_0]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h0, hlam, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h1265, hlam, p3987_0]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h1265, h3978, h3986, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h1561, hlam, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          rcases p3987_3 (m.d 0 1) (by simp) with h3993 | h3993
                          · linarith only [h0, h3993, hlam]
                          · rcases p3987_3 (m.d 0 2) (by simp) with h3995 | h3995
                            · rcases p3987_3 (m.d 0 3) (by simp) with h3996 | h3996
                              · linarith only [h2078, h3996, hlam]
                              · linarith only [h1265, h3996, hlam]
                            · linarith only [h0, h3995, hlam]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [hlam, p3987_0]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          rcases p3987_3 (m.d 0 1) (by simp) with h4001 | h4001
                          · linarith only [h0, h4001, hlam]
                          · rcases p3987_3 (m.d 0 2) (by simp) with h4003 | h4003
                            · rcases p3987_3 (m.d 0 3) (by simp) with h4004 | h4004
                              · linarith only [h2078, h4004, hlam]
                              · rcases p3987_3 (m.d 0 4) (by simp) with h4006 | h4006
                                · linarith only [h2079, h4006, hlam]
                                · linarith only [h2081, h4006, hlam]
                            · linarith only [h2078, h4003, hlam]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          rcases p3987_3 (m.d 0 1) (by simp) with h4010 | h4010
                          · linarith only [h0, h4010, hlam]
                          · rcases p3987_3 (m.d 0 2) (by simp) with h4012 | h4012
                            · rcases p3987_3 (m.d 0 3) (by simp) with h4013 | h4013
                              · linarith only [h2078, h4013, hlam]
                              · rcases p3987_3 (m.d 0 4) (by simp) with h4015 | h4015
                                · linarith only [h2079, h4015, hlam]
                                · rcases p3987_3 (m.d 0 5) (by simp) with h4017 | h4017
                                  · linarith only [h2080, h4017, hlam]
                                  · rcases h3bigk with h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c | h4019c
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h1265, hlam, p4019_1]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h0, h3675, h3879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3987_1, p4019_1, u2ehi2]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h2081, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3675, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h1265, hc01, hc13, hlam, hphi, p4019_1]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3978, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4019_1, u2ehi2]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3882, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3978, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h2078, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3880, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3981, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3983, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h2078, hc34, hlam, hphi, ht23, p4019_1, u2ehi2]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hc13, hc34, hlam, hphi, p4019_1]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht23, p4019_1, u2ehi2]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h1561, h3978, hc01, hc34, hlam, hphi, ht12, ht23, p4019_1]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h2078, hc35, hlam, hphi, ht23, p4019_1, u2ehi2]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h0, h1265, h2078, h3675, h3879, hc01, hc12, hc35, hlam, hphi, ht23, p3987_1, p4019_1, u2ehi2]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht23, p4019_1, u2ehi2]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [h3986, hlam, p4019_0]
                                    · have p4019_0 := h4019c.1
                                      have p4019_1 := h4019c.2.1
                                      have p4019_2 := h4019c.2.2.1
                                      have p4019_3 := h4019c.2.2.2
                                      linarith only [hlam, p4019_0]
                            · linarith only [h2079, h4012, hlam]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          rcases p3987_3 (m.d 0 1) (by simp) with h4046 | h4046
                          · linarith only [h0, h4046, hlam]
                          · rcases p3987_3 (m.d 0 2) (by simp) with h4048 | h4048
                            · rcases p3987_3 (m.d 0 3) (by simp) with h4049 | h4049
                              · linarith only [h2078, h4049, hlam]
                              · rcases p3987_3 (m.d 0 4) (by simp) with h4051 | h4051
                                · linarith only [h2079, h4051, hlam]
                                · linarith only [h3879, h4051, hlam]
                            · linarith only [h2080, h4048, hlam]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h2081, hc01, hc34, hlam, hphi, ht12, ht23, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h2078, hlam, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [hlam, p3987_0]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h2081, hlam, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h3675, hlam, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          rcases p3987_3 (m.d 0 1) (by simp) with h4060 | h4060
                          · linarith only [h4060, hlam, p3987_0]
                          · rcases p3987_3 (m.d 0 2) (by simp) with h4062 | h4062
                            · rcases p3987_3 (m.d 0 3) (by simp) with h4063 | h4063
                              · linarith only [h2081, h4063, hlam]
                              · linarith only [h1265, h4063, hlam]
                            · linarith only [h0, h4062, hlam]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h2079, hlam, p3987_0]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h2078, h2081, hc34, hlam, hphi, ht23, p3987_1, u2ehi2]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [hlam, p3987_0]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h2078, h2081, h3675, hc34, hlam, hphi, ht23, p3987_1, u2ehi2]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          rcases p3987_3 (m.d 0 1) (by simp) with h4071 | h4071
                          · linarith only [h1561, h4071, hlam]
                          · rcases p3987_3 (m.d 0 2) (by simp) with h4073 | h4073
                            · rcases p3987_3 (m.d 0 3) (by simp) with h4074 | h4074
                              · linarith only [h3675, h4074, hlam]
                              · linarith only [h1265, h4074, hlam]
                            · linarith only [h0, h4073, hlam]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h2080, hlam, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h1561, h2078, h3978, hc35, hlam, hphi, ht23, p3987_1, u2ehi2]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [h3879, hlam, p3987_1]
                        · have p3987_0 := h3987c.1
                          have p3987_1 := h3987c.2.1
                          have p3987_2 := h3987c.2.2.1
                          have p3987_3 := h3987c.2.2.2
                          linarith only [hlam, p3987_0]
                      · linarith only [h2078, h2081, h3986, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h2081, h3879, h3985, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h2081, h3879, h3881, h3980, hc34, hlam, hphi, ht23, u2ehi3]
        · linarith only [h0, h2078, h3881, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h2079, h3880, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4087 | h4087
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4088 | h4088
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4089 | h4089
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4090 | h4090
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4091 | h4091
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4092 | h4092
                · linarith only [h2078, h2081, h4092, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4094 | h4094
                  · linarith only [h0, h1265, h2078, h3675, h4094, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4096 | h4096
                    · linarith only [h2079, h3879, h4096, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4098 | h4098
                      · linarith only [h2078, h2081, h3879, h4098, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h2078, h2081, h4098, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h2078, h2081, h4089, h4091, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h2078, h2081, h4089, h4090, hc35, hlam, hphi, ht23, u2ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4103 | h4103
            · linarith only [h2078, h3675, h4089, h4103, hc34, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4105 | h4105
              · linarith only [h2078, h2081, h3879, h4089, h4105, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4107 | h4107
                · linarith only [h2078, h2081, h4107, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4109 | h4109
                  · linarith only [h1265, h4103, h4109, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4111 | h4111
                    · linarith only [h1265, h2078, h4089, h4105, h4111, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4113 | h4113
                      · linarith only [h1265, h2078, h4089, h4105, h4113, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h2078, h2081, h4113, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h0, h2079, h3879, h4088, hc45, hlam, hphi, ht23, ht34, u2ehi0]
      · linarith only [h0, h2078, h4087, hlam]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 3 4 (by decide) (by decide) with h2081 | h2081
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080 h2081

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2080 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  linarith only [h2078, h2080, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 2 5 (by decide) (by decide) with h2080 | h2080
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079 h2080

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2079 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  linarith only [h2078, h2079, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 2 4 (by decide) (by decide) with h2079 | h2079
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078 h2079

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2078 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 2 4 (by decide) (by decide) with h4120 | h4120
  · linarith only [h2078, h4120, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4122 | h4122
    · linarith only [h2078, h4122, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4124 | h4124
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4125 | h4125
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4126 | h4126
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4127 | h4127
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4128 | h4128
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4129 | h4129
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4130 | h4130
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4131 | h4131
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4132 | h4132
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4133 | h4133
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4134 | h4134
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4135 | h4135
                            · rcases h0bigk with h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h0, hlam, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h1265, hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h0, h4122, h4126, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h1561, hlam, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h2078, h4127, hc01, hc12, hlam, hphi, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h2078, hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4120, hlam, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4122, hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h2078, h4127, hc01, hc12, hlam, hphi, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h2078, h4127, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h2078, h4122, h4126, h4127, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h2078, h4122, h4127, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4120, h4127, h4132, hc01, hc12, hlam, hphi, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4120, h4127, h4132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4124, hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4120, h4122, h4127, h4132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4122, h4127, h4132, h4134, hc01, hc12, hlam, hphi, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4122, h4127, h4132, h4134, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4125, hlam, p4136_0]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [h4126, hlam, p4136_1]
                              · have p4136_0 := h4136c.1
                                have p4136_1 := h4136c.2.1
                                have p4136_2 := h4136c.2.2.1
                                have p4136_3 := h4136c.2.2.2
                                linarith only [hlam, p4136_0]
                            · rcases h0bigk with h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h0, hlam, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h1265, hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4126, h4135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h1561, hlam, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h2078, h4127, hc01, hc12, hlam, hphi, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h2078, hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4120, hlam, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4122, hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h2078, h4127, hc01, hc12, hlam, hphi, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h2078, h4127, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4162_1, u2ehi0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h2078, h4126, h4127, h4135, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h1561, h2078, h4127, hc01, hc12, hlam, hphi, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4120, h4127, h4132, hc01, hc12, hlam, hphi, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4120, h4127, h4132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4162_1, u2ehi0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4124, hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4120, h4122, h4127, h4132, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4162_1, u2ehi0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4122, h4127, h4132, h4134, hc01, hc12, hlam, hphi, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4122, h4127, h4132, h4134, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4162_1, u2ehi0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4125, hlam, p4162_0]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [h4126, hlam, p4162_1]
                              · have p4162_0 := h4162c.1
                                have p4162_1 := h4162c.2.1
                                have p4162_2 := h4162c.2.2.1
                                have p4162_3 := h4162c.2.2.2
                                linarith only [hlam, p4162_0]
                          · linarith only [h4120, h4134, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h2078, h4133, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2078, h4132, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h4120, h4124, h4126, h4128, h4131, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h2078, h4125, h4127, h4130, hlam]
                · linarith only [h2078, h4124, h4127, h4129, hlam]
              · linarith only [h4127, h4128, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4195 | h4195
              · linarith only [h4127, h4195, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4197 | h4197
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4198 | h4198
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4199 | h4199
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4200 | h4200
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4201 | h4201
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4202 | h4202
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4203 | h4203
                            · rcases h0bigk with h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c | h4204c
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h0, hlam, p4204_1]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h1265, hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h0, h4122, h4126, h4195, h4200, hc23, hlam, hphi, p4204_1, u2ehi0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h1561, hlam, p4204_1]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4122, hc01, hc25, hlam, hphi, ht12, p4204_1]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h2078, hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4120, hlam, p4204_1]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4122, hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                rcases p4204_3 (m.d 0 1) (by simp) with h4215 | h4215
                                · linarith only [h1265, h4215, hlam]
                                · rcases p4204_3 (m.d 0 2) (by simp) with h4217 | h4217
                                  · linarith only [h2078, h4217, hlam]
                                  · linarith only [h0, h4217, hlam]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h2078, hc23, hlam, hphi, p4204_1, u2ehi0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h2078, h4122, h4126, hc23, hlam, hphi, p4204_1, u2ehi0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h2078, h4122, hc23, hlam, hphi, p4204_1, u2ehi0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                rcases p4204_3 (m.d 0 1) (by simp) with h4224 | h4224
                                · linarith only [h4224, hlam, p4204_0]
                                · rcases p4204_3 (m.d 0 2) (by simp) with h4226 | h4226
                                  · linarith only [h4120, h4226, hlam]
                                  · linarith only [h0, h4226, hlam]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4120, hc24, hlam, hphi, p4204_1, u2ehi0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4124, hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h1265, h4122, h4124, h4127, hc23, hlam, hphi, p4204_1, u2ehi0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                rcases p4204_3 (m.d 0 1) (by simp) with h4233 | h4233
                                · linarith only [h1561, h4233, hlam]
                                · rcases p4204_3 (m.d 0 2) (by simp) with h4235 | h4235
                                  · linarith only [h4122, h4235, hlam]
                                  · linarith only [h0, h4235, hlam]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4122, h4200, h4202, hc23, hlam, hphi, p4204_1, u2ehi0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4125, hlam, p4204_0]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [h4126, hlam, p4204_1]
                              · have p4204_0 := h4204c.1
                                have p4204_1 := h4204c.2.1
                                have p4204_2 := h4204c.2.2.1
                                have p4204_3 := h4204c.2.2.2
                                linarith only [hlam, p4204_0]
                            · rcases h0bigk with h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h0, hlam, p4242_1]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1265, hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1561, h4126, hlam, p4242_1]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1561, hlam, p4242_1]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h2078, hc01, hc23, hlam, hphi, ht12, p4242_1]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h2078, hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h4120, hlam, p4242_1]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h4122, hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                rcases p4242_3 (m.d 0 1) (by simp) with h4253 | h4253
                                · linarith only [h1265, h4253, hlam]
                                · rcases p4242_3 (m.d 0 2) (by simp) with h4255 | h4255
                                  · linarith only [h2078, h4255, hlam]
                                  · linarith only [h0, h4255, hlam]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1265, h4127, hc23, hlam, hphi, p4242_1, u2ehi0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1265, h4120, h4127, hc23, hlam, hphi, p4242_1, u2ehi0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1265, h4122, h4127, hc23, hlam, hphi, p4242_1, u2ehi0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                rcases p4242_3 (m.d 0 1) (by simp) with h4262 | h4262
                                · linarith only [h4262, hlam, p4242_0]
                                · rcases p4242_3 (m.d 0 2) (by simp) with h4264 | h4264
                                  · linarith only [h4120, h4264, hlam]
                                  · linarith only [h0, h4264, hlam]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h4120, h4200, hc23, hlam, hphi, p4242_1, u2ehi0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h4124, hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1265, h4122, h4124, h4127, hc23, hlam, hphi, p4242_1, u2ehi0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                rcases p4242_3 (m.d 0 1) (by simp) with h4271 | h4271
                                · linarith only [h1561, h4271, hlam]
                                · rcases p4242_3 (m.d 0 2) (by simp) with h4273 | h4273
                                  · linarith only [h4122, h4273, hlam]
                                  · linarith only [h0, h4273, hlam]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h1561, h4195, h4199, h4200, hc23, hlam, hphi, p4242_1, u2ehi0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h4125, hlam, p4242_0]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [h4126, hlam, p4242_1]
                              · have p4242_0 := h4242c.1
                                have p4242_1 := h4242c.2.1
                                have p4242_2 := h4242c.2.2.1
                                have p4242_3 := h4242c.2.2.2
                                linarith only [hlam, p4242_0]
                          · linarith only [h4195, h4202, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                        · linarith only [h0, h4195, h4200, h4201, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2078, h4200, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h1265, h4124, h4126, h4195, h4199, hc01, hc13, hlam, hphi]
                  · linarith only [h1265, h4125, h4198, hlam]
                · linarith only [h1265, h4124, h4197, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4286 | h4286
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4287 | h4287
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4288 | h4288
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4289 | h4289
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4290 | h4290
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4291 | h4291
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4292 | h4292
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4293 | h4293
                          · linarith only [h4120, h4126, h4293, hc24, hlam, hphi, u2ehi0]
                          · linarith only [h4120, h4286, h4288, h4290, h4293, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h2078, h4125, h4292, hlam]
                      · linarith only [h2078, h4124, h4125, h4126, h4286, h4288, h4290, h4291, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h4120, h4287, h4290, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h1265, h4125, h4289, hlam]
                · linarith only [h2078, h4286, h4288, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h4286, h4287, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4302 | h4302
              · linarith only [h4286, h4302, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4304 | h4304
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4305 | h4305
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4306 | h4306
                    · linarith only [h4120, h4126, h4286, h4304, h4306, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4308 | h4308
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4309 | h4309
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4310 | h4310
                          · linarith only [h0, h4302, h4306, h4310, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h4120, h4310, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h2078, h4309, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1265, h4124, h4286, h4308, hlam]
                  · linarith only [h1265, h4125, h4305, hlam]
                · linarith only [h1265, h4124, h4304, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4317 | h4317
          · linarith only [h4124, h4125, h4317, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4319 | h4319
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4320 | h4320
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4321 | h4321
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4322 | h4322
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4323 | h4323
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4324 | h4324
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4325 | h4325
                        · linarith only [h2078, h4125, h4325, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2078, h4319, h4322, h4325, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h2078, h4124, h4125, h4319, h4322, h4324, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h4120, h4320, h4323, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h2078, h4319, h4322, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2078, h4124, h4319, h4321, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h2078, h4319, h4320, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4333 | h4333
              · linarith only [h4319, h4333, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4335 | h4335
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4336 | h4336
                  · linarith only [h2078, h4125, h4319, h4336, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4338 | h4338
                    · linarith only [h4122, h4317, h4335, h4336, h4338, hc35, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4340 | h4340
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4341 | h4341
                        · linarith only [h4333, h4335, h4336, h4341, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h2078, h4341, hc35, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h4124, h4319, h4340, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h1265, h4124, h4335, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4346 | h4346
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4347 | h4347
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4348 | h4348
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4349 | h4349
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4350 | h4350
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4351 | h4351
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4352 | h4352
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4353 | h4353
                      · linarith only [h4122, h4124, h4346, h4348, h4353, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h2078, h4353, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h4120, h4347, h4349, h4352, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h4124, h4346, h4351, hc13, hc34, hlam, hphi]
                · linarith only [h2078, h4348, h4350, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h2078, h4348, h4349, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4360 | h4360
              · linarith only [h4348, h4360, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4362 | h4362
                · linarith only [h2078, h4124, h4348, h4362, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4364 | h4364
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4365 | h4365
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4366 | h4366
                      · linarith only [h1265, h4122, h4346, h4362, h4366, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h2078, h4366, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h4124, h4346, h4347, h4360, h4365, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1265, h4346, h4364, hlam]
          · linarith only [h4124, h4346, h4347, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4372 | h4372
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4373 | h4373
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4374 | h4374
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4375 | h4375
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4376 | h4376
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4377 | h4377
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4378 | h4378
                      · linarith only [h2078, h4124, h4378, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h2078, h4373, h4375, h4378, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h4120, h4372, h4374, h4377, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h4124, h4375, h4376, hc03, hc35, hlam, hphi]
                · linarith only [h2078, h4373, h4375, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h2078, h4373, h4374, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4385 | h4385
              · linarith only [h4373, h4385, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4387 | h4387
                · linarith only [h2078, h4124, h4373, h4387, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4389 | h4389
                  · linarith only [h2078, h4346, h4387, h4389, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4391 | h4391
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4392 | h4392
                      · linarith only [h4373, h4387, h4392, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h2078, h4392, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h4124, h4372, h4385, h4391, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4396 | h4396
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4397 | h4397
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4398 | h4398
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4399 | h4399
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4400 | h4400
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4401 | h4401
                      · linarith only [h2078, h4124, h4396, h4401, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h2078, h4401, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h4120, h4397, h4400, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h2078, h4124, h4398, h4399, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2078, h4396, h4398, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h2078, h4396, h4397, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4408 | h4408
              · linarith only [h4396, h4408, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4410 | h4410
                · linarith only [h2078, h4124, h4396, h4410, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4412 | h4412
                  · linarith only [h2078, h4346, h4410, h4412, hc34, hlam, hphi, ht23, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4414 | h4414
                    · linarith only [h2078, h4124, h4372, h4408, h4414, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4416 | h4416
                      · linarith only [h2078, h4124, h4416, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h2078, h4416, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 2 3 (by decide) (by decide) with h2078 | h2078
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x0 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1_x1 m hb0 hb2 hb3 hg0 hg1265 h1561 h2078

set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1265 := hg1265
  rcases m.htr 0 1 5 (by decide) (by decide) with h1561 | h1561
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x0 m hb0 hb2 hb3 hg0 hg1265 h1561
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1_x1 m hb0 hb2 hb3 hg0 hg1265 h1561

end R2N4
