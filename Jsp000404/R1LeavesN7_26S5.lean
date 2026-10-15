import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3618 | h3618
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3619 | h3619
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3620 | h3620
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3621 | h3621
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3622 | h3622
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3623 | h3623
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3624 | h3624
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3625 | h3625
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3626 | h3626
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3627 | h3627
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3628 | h3628
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3629 | h3629
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3630 | h3630
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3631 | h3631
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3632 | h3632
                              · rcases h0bigk with h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c | h3633c
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h0, hlam, p3633_1]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3129, hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3354, hlam, p3633_1]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3354, h3622, h3624, h3627, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3633_1, u3ehi4]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h0, h3617, h3628, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3633_1, u3ehi4]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h0, h3354, h3617, h3621, h3628, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3633_1, u3ehi4]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h0, h3354, h3617, h3628, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3633_1, u3ehi4]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  rcases p3633_3 (m.d 0 1) (by simp) with h3643 | h3643
                                  · linarith only [h0, h3643, hlam]
                                  · linarith only [h3617, h3643, hlam]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3617, h3626, h3630, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3633_1, u3ehi4]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3618, hlam, p3633_1]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3129, h3354, h3617, h3624, h3626, h3630, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3633_1, u3ehi4]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  rcases p3633_3 (m.d 0 1) (by simp) with h3650 | h3650
                                  · linarith only [h3129, h3650, hlam]
                                  · linarith only [h3617, h3650, hlam]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3617, h3626, h3630, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p3633_1, u3ehi4]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3619, hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3621, hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  rcases p3633_3 (m.d 0 1) (by simp) with h3657 | h3657
                                  · linarith only [h3354, h3657, hlam]
                                  · linarith only [h3617, h3657, hlam]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3617, hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3620, hlam, p3633_1]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3622, hlam, p3633_0]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [h3623, hlam, p3633_1]
                                · have p3633_0 := h3633c.1
                                  have p3633_1 := h3633c.2.1
                                  have p3633_2 := h3633c.2.2.1
                                  have p3633_3 := h3633c.2.2.2
                                  linarith only [hlam, p3633_0]
                              · linarith only [h0, h3618, h3629, h3631, h3632, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3666 | h3666
                              · linarith only [h3629, h3631, h3666, hlam]
                              · rcases h0bigk with h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c | h3668c
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h0, hlam, p3668_1]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3129, hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3354, hlam, p3668_1]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3623, h3629, h3631, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h0, h3617, h3626, h3629, h3631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h0, h3129, h3617, h3626, h3629, h3631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h0, h3354, h3617, h3626, h3629, h3631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h0, h3623, h3629, h3631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3617, h3626, h3629, h3631, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3618, hlam, p3668_1]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3129, h3354, h3617, h3624, h3626, h3629, h3631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3129, h3623, h3624, h3629, h3631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3617, h3626, h3629, h3631, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3619, hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3621, hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3354, h3623, h3624, h3627, h3629, h3631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3668_1, u3ehi3]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3617, hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3620, hlam, p3668_1]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3622, hlam, p3668_0]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [h3623, hlam, p3668_1]
                                · have p3668_0 := h3668c.1
                                  have p3668_1 := h3668c.2.1
                                  have p3668_2 := h3668c.2.2.1
                                  have p3668_3 := h3668c.2.2.2
                                  linarith only [hlam, p3668_0]
                          · linarith only [h3354, h3617, h3624, h3627, h3628, h3630, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3695 | h3695
                          · linarith only [h3629, h3695, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h3354, h3617, h3624, h3627, h3628, h3695, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h3129, h3621, h3628, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3129, h3617, h3618, h3621, h3622, h3627, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h0, h3620, h3626, hlam]
                · linarith only [h0, h3619, h3625, hlam]
              · linarith only [h0, h3618, h3624, hlam]
            · linarith only [h3354, h3617, h3623, hlam]
          · linarith only [h3621, h3622, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3705 | h3705
          · linarith only [h3621, h3705, hc34, hlam, hphi, u3ehi4]
          · linarith only [h3129, h3617, h3705, hlam]
      · linarith only [h0, h3617, h3620, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3709 | h3709
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3710 | h3710
        · linarith only [h3618, h3619, h3710, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3712 | h3712
          · linarith only [h3710, h3712, hc34, hlam, hphi, u3ehi4]
          · linarith only [h3129, h3617, h3712, hlam]
      · linarith only [h0, h3617, h3709, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3716 | h3716
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3717 | h3717
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3718 | h3718
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3719 | h3719
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3720 | h3720
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3721 | h3721
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3722 | h3722
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3723 | h3723
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3724 | h3724
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3725 | h3725
                      · linarith only [h3354, h3617, h3618, h3716, h3721, h3725, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h3129, h3718, h3725, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3618, h3716, h3718, h3721, h3724, hlam]
                  · linarith only [h3354, h3617, h3618, h3716, h3719, h3721, h3723, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h3618, h3716, h3721, h3722, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3731 | h3731
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3732 | h3732
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3733 | h3733
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3734 | h3734
                      · linarith only [h0, h3617, h3721, h3734, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h3129, h3718, h3734, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3354, h3617, h3719, h3721, h3731, h3733, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h3717, h3732, hlam]
                · linarith only [h0, h3716, h3731, hlam]
            · linarith only [h3354, h3617, h3720, hlam]
          · linarith only [h3718, h3719, hc35, hlam, hphi, u3ehi3]
        · linarith only [h3618, h3716, h3718, hlam]
      · linarith only [h0, h3617, h3717, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3744 | h3744
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3745 | h3745
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3746 | h3746
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3747 | h3747
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3748 | h3748
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3749 | h3749
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3750 | h3750
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3751 | h3751
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3752 | h3752
                      · linarith only [h0, h3617, h3618, h3748, h3752, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h3129, h3745, h3752, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3618, h3745, h3748, h3751, hlam]
                  · linarith only [h3618, h3745, h3748, h3750, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h3617, h3618, h3746, h3748, h3749, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3758 | h3758
                · linarith only [h0, h3617, h3716, h3746, h3748, h3758, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3760 | h3760
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3761 | h3761
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3762 | h3762
                      · linarith only [h0, h3617, h3748, h3762, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h3129, h3745, h3762, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3129, h3745, h3761, hlam]
                  · linarith only [h0, h3617, h3744, h3746, h3760, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
            · linarith only [h0, h3617, h3716, h3747, hlam]
          · linarith only [h3745, h3746, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3769 | h3769
          · linarith only [h3745, h3769, hc34, hlam, hphi, u3ehi4]
          · linarith only [h3129, h3617, h3769, hlam]
      · linarith only [h0, h3617, h3744, hlam]

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3774 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3775 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3776 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h3777 | h3777
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3778 | h3778
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3779 | h3779
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3780 | h3780
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3781 | h3781
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3782 | h3782
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3783 | h3783
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3784 | h3784
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3785 | h3785
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3786 | h3786
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3787 | h3787
                      · rcases h0bigk with h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h0, hlam, p3788_1]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3129, hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3354, hlam, p3788_1]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3617, hlam, p3788_1]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3794 | h3794
                          · linarith only [h0, h3794, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3796 | h3796
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3797 | h3797
                              · linarith only [h3773, h3797, hlam]
                              · linarith only [h3129, h3797, hlam]
                            · linarith only [h0, h3796, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h0, h3773, h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3788_1, u3ehi4]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3803 | h3803
                          · linarith only [h0, h3803, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3805 | h3805
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3806 | h3806
                              · linarith only [h3773, h3806, hlam]
                              · linarith only [h3776, h3806, hlam]
                            · linarith only [h3774, h3805, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3810 | h3810
                          · linarith only [h0, h3810, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3812 | h3812
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3813 | h3813
                              · linarith only [h3773, h3813, hlam]
                              · linarith only [h3777, h3813, hlam]
                            · linarith only [h3775, h3812, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3817 | h3817
                          · linarith only [h3129, h3817, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3819 | h3819
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3820 | h3820
                              · rcases p3788_3 (m.d 0 4) (by simp) with h3821 | h3821
                                · linarith only [h3776, h3821, hlam]
                                · linarith only [h3354, h3821, hlam]
                              · linarith only [h3129, h3820, hlam]
                            · linarith only [h0, h3819, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3773, hlam, p3788_1]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3828 | h3828
                          · linarith only [h3129, h3828, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3830 | h3830
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3831 | h3831
                              · rcases p3788_3 (m.d 0 4) (by simp) with h3832 | h3832
                                · linarith only [h3776, h3832, hlam]
                                · rcases p3788_3 (m.d 0 5) (by simp) with h3834 | h3834
                                  · linarith only [h3777, h3834, hlam]
                                  · rcases h2bigk with h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c | h3836c
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h0, hlam, p3836_1]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h0, h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3836_1, u3ehi4]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      rcases p3836_3 (m.d 0 2) (by simp) with h3840 | h3840
                                      · rcases p3836_3 (m.d 1 2) (by simp) with h3841 | h3841
                                        · rcases p3836_3 (m.d 2 3) (by simp) with h3842 | h3842
                                          · linarith only [h3773, h3842, hlam]
                                          · linarith only [h3784, h3842, hlam]
                                        · linarith only [h3780, h3841, hlam]
                                      · linarith only [h3840, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      rcases p3836_3 (m.d 0 2) (by simp) with h3847 | h3847
                                      · rcases p3836_3 (m.d 1 2) (by simp) with h3848 | h3848
                                        · rcases p3836_3 (m.d 2 3) (by simp) with h3849 | h3849
                                          · linarith only [h3773, h3849, hlam]
                                          · linarith only [h3785, h3849, hlam]
                                        · linarith only [h3781, h3848, hlam]
                                      · linarith only [h3847, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3617, h3773, h3778, hc01, hc12, hlam, hphi, p3788_1, p3836_1]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3836_1, u3ehi4]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      rcases p3836_3 (m.d 0 2) (by simp) with h3857 | h3857
                                      · linarith only [h0, h3857, hlam]
                                      · linarith only [h3774, h3857, hlam]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      rcases p3836_3 (m.d 0 2) (by simp) with h3860 | h3860
                                      · linarith only [h0, h3860, hlam]
                                      · linarith only [h3775, h3860, hlam]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3773, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3779, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3773, h3784, h3787, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3836_1, u3ehi4]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h0, h3773, h3785, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3836_1, u3ehi4]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3774, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3780, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3784, hlam, p3836_1]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3774, h3785, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3788_1, p3836_1, u3ehi4]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3775, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3781, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3785, hlam, p3836_1]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [h3786, hlam, p3836_0]
                                    · have p3836_0 := h3836c.1
                                      have p3836_1 := h3836c.2.1
                                      have p3836_2 := h3836c.2.2.1
                                      have p3836_3 := h3836c.2.2.2
                                      linarith only [hlam, p3836_0]
                              · linarith only [h3776, h3831, hlam]
                            · linarith only [h3774, h3830, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3880 | h3880
                          · linarith only [h3129, h3880, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3882 | h3882
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3883 | h3883
                              · rcases p3788_3 (m.d 0 4) (by simp) with h3884 | h3884
                                · linarith only [h3776, h3884, hlam]
                                · linarith only [h3778, h3884, hlam]
                              · linarith only [h3777, h3883, hlam]
                            · linarith only [h3775, h3882, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3889 | h3889
                          · linarith only [h3354, h3889, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3891 | h3891
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3892 | h3892
                              · rcases p3788_3 (m.d 0 4) (by simp) with h3893 | h3893
                                · rcases p3788_3 (m.d 0 5) (by simp) with h3894 | h3894
                                  · linarith only [h3778, h3894, hlam]
                                  · linarith only [h3617, h3894, hlam]
                                · linarith only [h3354, h3893, hlam]
                              · linarith only [h3129, h3892, hlam]
                            · linarith only [h0, h3891, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3774, hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3776, hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3903 | h3903
                          · linarith only [h3354, h3903, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3905 | h3905
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3906 | h3906
                              · rcases p3788_3 (m.d 0 4) (by simp) with h3907 | h3907
                                · rcases p3788_3 (m.d 0 5) (by simp) with h3908 | h3908
                                  · linarith only [h3778, h3908, hlam]
                                  · rcases h2bigk with h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h0, hlam, p3910_1]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h0, h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3910_1, u3ehi4]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      rcases p3910_3 (m.d 0 2) (by simp) with h3914 | h3914
                                      · rcases p3910_3 (m.d 1 2) (by simp) with h3915 | h3915
                                        · rcases p3910_3 (m.d 2 3) (by simp) with h3916 | h3916
                                          · linarith only [h3773, h3916, hlam]
                                          · linarith only [h3784, h3916, hlam]
                                        · linarith only [h3780, h3915, hlam]
                                      · linarith only [h3914, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      rcases p3910_3 (m.d 0 2) (by simp) with h3921 | h3921
                                      · rcases p3910_3 (m.d 1 2) (by simp) with h3922 | h3922
                                        · rcases p3910_3 (m.d 2 3) (by simp) with h3923 | h3923
                                          · linarith only [h3773, h3923, hlam]
                                          · linarith only [h3785, h3923, hlam]
                                        · linarith only [h3781, h3922, hlam]
                                      · linarith only [h3921, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3773, h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3910_1, u3ehi4]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3910_1, u3ehi4]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      rcases p3910_3 (m.d 0 2) (by simp) with h3931 | h3931
                                      · linarith only [h0, h3931, hlam]
                                      · linarith only [h3774, h3931, hlam]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      rcases p3910_3 (m.d 0 2) (by simp) with h3934 | h3934
                                      · linarith only [h0, h3934, hlam]
                                      · linarith only [h3775, h3934, hlam]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3773, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3779, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3773, h3784, h3787, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3910_1, u3ehi4]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h0, h3773, h3785, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3910_1, u3ehi4]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3774, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3780, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3784, hlam, p3910_1]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h0, h3774, h3785, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3910_1, u3ehi4]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3775, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3781, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3785, hlam, p3910_1]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [h3786, hlam, p3910_0]
                                    · have p3910_0 := h3910c.1
                                      have p3910_1 := h3910c.2.1
                                      have p3910_2 := h3910c.2.2.1
                                      have p3910_3 := h3910c.2.2.2
                                      linarith only [hlam, p3910_0]
                                · linarith only [h3778, h3907, hlam]
                              · linarith only [h3777, h3906, hlam]
                            · linarith only [h3775, h3905, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          rcases p3788_3 (m.d 0 1) (by simp) with h3955 | h3955
                          · linarith only [h3617, h3955, hlam]
                          · rcases p3788_3 (m.d 0 2) (by simp) with h3957 | h3957
                            · rcases p3788_3 (m.d 0 3) (by simp) with h3958 | h3958
                              · rcases p3788_3 (m.d 0 4) (by simp) with h3959 | h3959
                                · rcases p3788_3 (m.d 0 5) (by simp) with h3960 | h3960
                                  · rcases h2bigk with h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c | h3961c
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h0, hlam, p3961_1]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h0, h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3961_1, u3ehi4]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      rcases p3961_3 (m.d 0 2) (by simp) with h3965 | h3965
                                      · rcases p3961_3 (m.d 1 2) (by simp) with h3966 | h3966
                                        · rcases p3961_3 (m.d 2 3) (by simp) with h3967 | h3967
                                          · linarith only [h3773, h3967, hlam]
                                          · linarith only [h3784, h3967, hlam]
                                        · linarith only [h3780, h3966, hlam]
                                      · linarith only [h3965, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      rcases p3961_3 (m.d 0 2) (by simp) with h3972 | h3972
                                      · rcases p3961_3 (m.d 1 2) (by simp) with h3973 | h3973
                                        · rcases p3961_3 (m.d 2 3) (by simp) with h3974 | h3974
                                          · linarith only [h3773, h3974, hlam]
                                          · linarith only [h3785, h3974, hlam]
                                        · linarith only [h3781, h3973, hlam]
                                      · linarith only [h3972, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3773, h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3961_1, u3ehi4]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3784, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3961_1, u3ehi4]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      rcases p3961_3 (m.d 0 2) (by simp) with h3982 | h3982
                                      · linarith only [h0, h3982, hlam]
                                      · linarith only [h3774, h3982, hlam]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      rcases p3961_3 (m.d 0 2) (by simp) with h3985 | h3985
                                      · linarith only [h0, h3985, hlam]
                                      · linarith only [h3775, h3985, hlam]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3773, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3779, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3773, h3784, h3787, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3961_1, u3ehi4]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h0, h3773, h3785, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3961_1, u3ehi4]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3774, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3780, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3784, hlam, p3961_1]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h0, h3774, h3785, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3961_1, u3ehi4]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3775, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3781, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3785, hlam, p3961_1]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [h3786, hlam, p3961_0]
                                    · have p3961_0 := h3961c.1
                                      have p3961_1 := h3961c.2.1
                                      have p3961_2 := h3961c.2.2.1
                                      have p3961_3 := h3961c.2.2.2
                                      linarith only [hlam, p3961_0]
                                  · linarith only [h3617, h3960, hlam]
                                · linarith only [h3354, h3959, hlam]
                              · linarith only [h3129, h3958, hlam]
                            · linarith only [h0, h3957, hlam]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3775, hlam, p3788_1]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3777, hlam, p3788_0]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [h3778, hlam, p3788_1]
                        · have p3788_0 := h3788c.1
                          have p3788_1 := h3788c.2.1
                          have p3788_2 := h3788c.2.2.1
                          have p3788_3 := h3788c.2.2.2
                          linarith only [hlam, p3788_0]
                      · linarith only [h0, h3773, h3784, h3786, h3787, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4012 | h4012
                      · linarith only [h0, h3773, h3784, h3786, h4012, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c | h4014c
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h0, hlam, p4014_1]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3129, hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3354, hlam, p4014_1]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3617, hlam, p4014_1]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          rcases p4014_3 (m.d 0 1) (by simp) with h4020 | h4020
                          · linarith only [h0, h4020, hlam]
                          · rcases p4014_3 (m.d 0 2) (by simp) with h4022 | h4022
                            · rcases p4014_3 (m.d 0 3) (by simp) with h4023 | h4023
                              · linarith only [h3773, h4023, hlam]
                              · linarith only [h3129, h4023, hlam]
                            · linarith only [h0, h4022, hlam]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h0, h3776, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4014_1, u3ehi3]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h0, h3778, h3784, h3786, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4014_1, u3ehi3]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h0, h3778, h3784, h3786, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4014_1, u3ehi3]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          rcases p4014_3 (m.d 0 1) (by simp) with h4031 | h4031
                          · linarith only [h3129, h4031, hlam]
                          · rcases p4014_3 (m.d 0 2) (by simp) with h4033 | h4033
                            · rcases p4014_3 (m.d 0 3) (by simp) with h4034 | h4034
                              · rcases p4014_3 (m.d 0 4) (by simp) with h4035 | h4035
                                · linarith only [h3776, h4035, hlam]
                                · linarith only [h3354, h4035, hlam]
                              · linarith only [h3129, h4034, hlam]
                            · linarith only [h0, h4033, hlam]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3773, hlam, p4014_1]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3778, h3784, h3786, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p4014_1, u3ehi3]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3129, h3778, h3779, h3784, h3786, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4014_1, u3ehi3]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          rcases p4014_3 (m.d 0 1) (by simp) with h4044 | h4044
                          · linarith only [h3354, h4044, hlam]
                          · rcases p4014_3 (m.d 0 2) (by simp) with h4046 | h4046
                            · rcases p4014_3 (m.d 0 3) (by simp) with h4047 | h4047
                              · rcases p4014_3 (m.d 0 4) (by simp) with h4048 | h4048
                                · rcases p4014_3 (m.d 0 5) (by simp) with h4049 | h4049
                                  · linarith only [h3778, h4049, hlam]
                                  · linarith only [h3617, h4049, hlam]
                                · linarith only [h3354, h4048, hlam]
                              · linarith only [h3129, h4047, hlam]
                            · linarith only [h0, h4046, hlam]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3774, hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3776, hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3778, h3784, h3786, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p4014_1, u3ehi3]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          rcases p4014_3 (m.d 0 1) (by simp) with h4059 | h4059
                          · linarith only [h3617, h4059, hlam]
                          · rcases p4014_3 (m.d 0 2) (by simp) with h4061 | h4061
                            · rcases p4014_3 (m.d 0 3) (by simp) with h4062 | h4062
                              · rcases p4014_3 (m.d 0 4) (by simp) with h4063 | h4063
                                · rcases p4014_3 (m.d 0 5) (by simp) with h4064 | h4064
                                  · rcases h2bigk with h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h0, hlam, p4065_1]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h0, h3784, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4065_1, u3ehi3]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      rcases p4065_3 (m.d 0 2) (by simp) with h4069 | h4069
                                      · rcases p4065_3 (m.d 1 2) (by simp) with h4070 | h4070
                                        · rcases p4065_3 (m.d 2 3) (by simp) with h4071 | h4071
                                          · linarith only [h3773, h4071, hlam]
                                          · linarith only [h3784, h4071, hlam]
                                        · linarith only [h3780, h4070, hlam]
                                      · linarith only [h4069, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      rcases p4065_3 (m.d 0 2) (by simp) with h4076 | h4076
                                      · rcases p4065_3 (m.d 1 2) (by simp) with h4077 | h4077
                                        · rcases p4065_3 (m.d 2 3) (by simp) with h4078 | h4078
                                          · linarith only [h3773, h4078, hlam]
                                          · linarith only [h3785, h4078, hlam]
                                        · linarith only [h3781, h4077, hlam]
                                      · linarith only [h4076, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3773, h3785, h4012, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4065_1, u3ehi3]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3785, h4012, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4065_1, u3ehi3]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      rcases p4065_3 (m.d 0 2) (by simp) with h4086 | h4086
                                      · linarith only [h0, h4086, hlam]
                                      · linarith only [h3774, h4086, hlam]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      rcases p4065_3 (m.d 0 2) (by simp) with h4089 | h4089
                                      · linarith only [h0, h4089, hlam]
                                      · linarith only [h3775, h4089, hlam]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3773, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3779, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3773, h3784, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p4065_1, u3ehi3]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h0, h3773, h3784, h3786, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4065_1, u3ehi3]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3774, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3780, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3784, hlam, p4065_1]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3786, hlam, p4065_1]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3775, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3781, hlam, p4065_0]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h3785, hlam, p4065_1]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [h0, h3775, h3784, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4065_1, u3ehi3]
                                    · have p4065_0 := h4065c.1
                                      have p4065_1 := h4065c.2.1
                                      have p4065_2 := h4065c.2.2.1
                                      have p4065_3 := h4065c.2.2.2
                                      linarith only [hlam, p4065_0]
                                  · linarith only [h3617, h4064, hlam]
                                · linarith only [h3354, h4063, hlam]
                              · linarith only [h3129, h4062, hlam]
                            · linarith only [h0, h4061, hlam]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3775, hlam, p4014_1]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3777, hlam, p4014_0]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [h3778, hlam, p4014_1]
                        · have p4014_0 := h4014c.1
                          have p4014_1 := h4014c.2.1
                          have p4014_2 := h4014c.2.2.1
                          have p4014_3 := h4014c.2.2.2
                          linarith only [hlam, p4014_0]
                  · linarith only [h3777, h3784, h3785, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4116 | h4116
                  · linarith only [h3784, h4116, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4118 | h4118
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4119 | h4119
                      · rcases h0bigk with h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h0, hlam, p4120_1]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3129, hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3354, hlam, p4120_1]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3617, hlam, p4120_1]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          rcases p4120_3 (m.d 0 1) (by simp) with h4126 | h4126
                          · linarith only [h0, h4126, hlam]
                          · rcases p4120_3 (m.d 0 2) (by simp) with h4128 | h4128
                            · rcases p4120_3 (m.d 0 3) (by simp) with h4129 | h4129
                              · linarith only [h3773, h4129, hlam]
                              · linarith only [h3129, h4129, hlam]
                            · linarith only [h0, h4128, hlam]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h0, h3776, h4116, h4119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4120_1, u3ehi2]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h0, h3776, h4116, h4119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4120_1, u3ehi2]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h0, h3777, h4116, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4120_1, u3ehi2]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          rcases p4120_3 (m.d 0 1) (by simp) with h4137 | h4137
                          · linarith only [h3129, h4137, hlam]
                          · rcases p4120_3 (m.d 0 2) (by simp) with h4139 | h4139
                            · rcases p4120_3 (m.d 0 3) (by simp) with h4140 | h4140
                              · rcases p4120_3 (m.d 0 4) (by simp) with h4141 | h4141
                                · linarith only [h3776, h4141, hlam]
                                · linarith only [h3354, h4141, hlam]
                              · linarith only [h3129, h4140, hlam]
                            · linarith only [h0, h4139, hlam]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3773, hlam, p4120_1]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3776, h4116, h4119, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p4120_1, u3ehi2]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3129, h3777, h3779, h4116, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4120_1, u3ehi2]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          rcases p4120_3 (m.d 0 1) (by simp) with h4150 | h4150
                          · linarith only [h3354, h4150, hlam]
                          · rcases p4120_3 (m.d 0 2) (by simp) with h4152 | h4152
                            · rcases p4120_3 (m.d 0 3) (by simp) with h4153 | h4153
                              · rcases p4120_3 (m.d 0 4) (by simp) with h4154 | h4154
                                · rcases p4120_3 (m.d 0 5) (by simp) with h4155 | h4155
                                  · linarith only [h3778, h4155, hlam]
                                  · linarith only [h3617, h4155, hlam]
                                · linarith only [h3354, h4154, hlam]
                              · linarith only [h3129, h4153, hlam]
                            · linarith only [h0, h4152, hlam]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3774, hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3776, hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3777, h4116, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p4120_1, u3ehi2]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          rcases p4120_3 (m.d 0 1) (by simp) with h4165 | h4165
                          · linarith only [h3617, h4165, hlam]
                          · rcases p4120_3 (m.d 0 2) (by simp) with h4167 | h4167
                            · rcases p4120_3 (m.d 0 3) (by simp) with h4168 | h4168
                              · rcases p4120_3 (m.d 0 4) (by simp) with h4169 | h4169
                                · rcases p4120_3 (m.d 0 5) (by simp) with h4170 | h4170
                                  · rcases h2bigk with h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c | h4171c
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h0, hlam, p4171_1]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      rcases p4171_3 (m.d 0 2) (by simp) with h4174 | h4174
                                      · rcases p4171_3 (m.d 1 2) (by simp) with h4175 | h4175
                                        · rcases p4171_3 (m.d 2 3) (by simp) with h4176 | h4176
                                          · linarith only [h4176, hlam, p4171_0]
                                          · rcases p4171_3 (m.d 2 4) (by simp) with h4178 | h4178
                                            · linarith only [h3774, h4178, hlam]
                                            · linarith only [h3784, h4178, hlam]
                                        · linarith only [h3779, h4175, hlam]
                                      · linarith only [h4174, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      rcases p4171_3 (m.d 0 2) (by simp) with h4183 | h4183
                                      · rcases p4171_3 (m.d 1 2) (by simp) with h4184 | h4184
                                        · rcases p4171_3 (m.d 2 3) (by simp) with h4185 | h4185
                                          · linarith only [h3773, h4185, hlam]
                                          · rcases p4171_3 (m.d 2 4) (by simp) with h4187 | h4187
                                            · linarith only [h4187, hlam, p4171_0]
                                            · rcases p4171_3 (m.d 2 5) (by simp) with h4189 | h4189
                                              · linarith only [h3775, h4189, hlam]
                                              · rcases h3bigk with h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c | h4191c
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3129, hlam, p4191_1]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  rcases p4191_3 (m.d 0 3) (by simp) with h4194 | h4194
                                                  · rcases p4191_3 (m.d 1 3) (by simp) with h4195 | h4195
                                                    · rcases p4191_3 (m.d 2 3) (by simp) with h4196 | h4196
                                                      · linarith only [h3773, h4196, hlam]
                                                      · rcases p4191_3 (m.d 3 4) (by simp) with h4198 | h4198
                                                        · linarith only [h3776, h4198, hlam]
                                                        · linarith only [h3784, h4198, hlam]
                                                    · linarith only [h3779, h4195, hlam]
                                                  · linarith only [h3773, h4194, hlam]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3129, h3779, h4116, h4119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3129, h3779, h4116, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3776, h3779, h4116, h4119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  rcases p4191_3 (m.d 0 3) (by simp) with h4207 | h4207
                                                  · linarith only [h3129, h4207, hlam]
                                                  · linarith only [h3773, h4207, hlam]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3779, h4116, h4119, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3779, h4116, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3773, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3779, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3784, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h4116, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3776, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3782, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3776, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3129, h3776, h3779, h4116, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3777, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h3783, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [hc35, hlam, hphi, p4191_1, u3ehi2]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [h4119, hlam, p4191_0]
                                                · have p4191_0 := h4191c.1
                                                  have p4191_1 := h4191c.2.1
                                                  have p4191_2 := h4191c.2.2.1
                                                  have p4191_3 := h4191c.2.2.2
                                                  linarith only [hlam, p4191_0]
                                        · linarith only [h3780, h4184, hlam]
                                      · linarith only [h4183, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      rcases p4171_3 (m.d 0 2) (by simp) with h4229 | h4229
                                      · rcases p4171_3 (m.d 1 2) (by simp) with h4230 | h4230
                                        · rcases p4171_3 (m.d 2 3) (by simp) with h4231 | h4231
                                          · linarith only [h3773, h4231, hlam]
                                          · rcases p4171_3 (m.d 2 4) (by simp) with h4233 | h4233
                                            · linarith only [h3774, h4233, hlam]
                                            · linarith only [h4118, h4233, hlam]
                                        · linarith only [h3781, h4230, hlam]
                                      · linarith only [h4229, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3773, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4171_1, u3ehi2]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      rcases p4171_3 (m.d 0 2) (by simp) with h4240 | h4240
                                      · linarith only [h0, h4240, hlam]
                                      · linarith only [h3773, h4240, hlam]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      rcases p4171_3 (m.d 0 2) (by simp) with h4243 | h4243
                                      · linarith only [h0, h4243, hlam]
                                      · linarith only [h3774, h4243, hlam]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      rcases p4171_3 (m.d 0 2) (by simp) with h4246 | h4246
                                      · linarith only [h0, h4246, hlam]
                                      · linarith only [h3775, h4246, hlam]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3773, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3779, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3784, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h4116, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3774, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3780, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3774, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p4171_1, u3ehi2]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3129, h3776, h3779, h3784, h4116, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4171_1, u3ehi2]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3775, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h3781, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h0, h3775, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4171_1, u3ehi2]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [h4118, hlam, p4171_0]
                                    · have p4171_0 := h4171c.1
                                      have p4171_1 := h4171c.2.1
                                      have p4171_2 := h4171c.2.2.1
                                      have p4171_3 := h4171c.2.2.2
                                      linarith only [hlam, p4171_0]
                                  · linarith only [h3617, h4170, hlam]
                                · linarith only [h3354, h4169, hlam]
                              · linarith only [h3129, h4168, hlam]
                            · linarith only [h0, h4167, hlam]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3775, hlam, p4120_1]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3777, hlam, p4120_0]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [h3778, hlam, p4120_1]
                        · have p4120_0 := h4120c.1
                          have p4120_1 := h4120c.2.1
                          have p4120_2 := h4120c.2.2.1
                          have p4120_3 := h4120c.2.2.2
                          linarith only [hlam, p4120_0]
                      · linarith only [h3784, h4118, h4119, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4273 | h4273
                      · linarith only [h3129, h3776, h3779, h3784, h4118, h4273, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h3129, h3776, h3778, h3779, h3784, h4273, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h3129, h3776, h3783, hc35, hlam, hphi, u3ehi3]
            · linarith only [h0, h3129, h3773, h3776, h3782, hc01, hc12, hlam, hphi]
          · linarith only [h0, h3775, h3781, hlam]
        · linarith only [h0, h3774, h3780, hlam]
      · linarith only [h0, h3773, h3779, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4281 | h4281
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4282 | h4282
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4283 | h4283
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4284 | h4284
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4285 | h4285
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4286 | h4286
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4287 | h4287
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4288 | h4288
                    · linarith only [h3774, h3778, h4288, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4290 | h4290
                      · linarith only [h3773, h3778, h4286, h4290, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h0, hlam, p4292_1]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3129, hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3354, hlam, p4292_1]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3617, hlam, p4292_1]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          rcases p4292_3 (m.d 0 1) (by simp) with h4298 | h4298
                          · linarith only [h0, h4298, hlam]
                          · rcases p4292_3 (m.d 0 2) (by simp) with h4300 | h4300
                            · rcases p4292_3 (m.d 0 3) (by simp) with h4301 | h4301
                              · linarith only [h3773, h4301, hlam]
                              · linarith only [h3129, h4301, hlam]
                            · linarith only [h0, h4300, hlam]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h0, h3773, h4287, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4292_1, u3ehi4]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          rcases p4292_3 (m.d 0 1) (by simp) with h4307 | h4307
                          · linarith only [h0, h4307, hlam]
                          · rcases p4292_3 (m.d 0 2) (by simp) with h4309 | h4309
                            · rcases p4292_3 (m.d 0 3) (by simp) with h4310 | h4310
                              · linarith only [h3773, h4310, hlam]
                              · linarith only [h3776, h4310, hlam]
                            · linarith only [h3774, h4309, hlam]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          rcases p4292_3 (m.d 0 1) (by simp) with h4314 | h4314
                          · linarith only [h0, h4314, hlam]
                          · rcases p4292_3 (m.d 0 2) (by simp) with h4316 | h4316
                            · rcases p4292_3 (m.d 0 3) (by simp) with h4317 | h4317
                              · linarith only [h3773, h4317, hlam]
                              · linarith only [h3777, h4317, hlam]
                            · linarith only [h3775, h4316, hlam]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          rcases p4292_3 (m.d 0 1) (by simp) with h4321 | h4321
                          · linarith only [h3129, h4321, hlam]
                          · rcases p4292_3 (m.d 0 2) (by simp) with h4323 | h4323
                            · rcases p4292_3 (m.d 0 3) (by simp) with h4324 | h4324
                              · rcases p4292_3 (m.d 0 4) (by simp) with h4325 | h4325
                                · linarith only [h3776, h4325, hlam]
                                · linarith only [h3354, h4325, hlam]
                              · linarith only [h3129, h4324, hlam]
                            · linarith only [h0, h4323, hlam]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3773, hlam, p4292_1]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          rcases p4292_3 (m.d 0 1) (by simp) with h4332 | h4332
                          · linarith only [h3129, h4332, hlam]
                          · rcases p4292_3 (m.d 0 2) (by simp) with h4334 | h4334
                            · rcases p4292_3 (m.d 0 3) (by simp) with h4335 | h4335
                              · rcases p4292_3 (m.d 0 4) (by simp) with h4336 | h4336
                                · linarith only [h3776, h4336, hlam]
                                · rcases p4292_3 (m.d 0 5) (by simp) with h4338 | h4338
                                  · linarith only [h3777, h4338, hlam]
                                  · linarith only [h3778, h4338, hlam]
                              · linarith only [h3776, h4335, hlam]
                            · linarith only [h3774, h4334, hlam]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          rcases p4292_3 (m.d 0 1) (by simp) with h4343 | h4343
                          · linarith only [h3129, h4343, hlam]
                          · rcases p4292_3 (m.d 0 2) (by simp) with h4345 | h4345
                            · rcases p4292_3 (m.d 0 3) (by simp) with h4346 | h4346
                              · rcases p4292_3 (m.d 0 4) (by simp) with h4347 | h4347
                                · linarith only [h3776, h4347, hlam]
                                · rcases p4292_3 (m.d 0 5) (by simp) with h4349 | h4349
                                  · linarith only [h3777, h4349, hlam]
                                  · rcases h2bigk with h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c | h4351c
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h0, hlam, p4351_1]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h0, h4287, h4290, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4351_1, u3ehi3]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      rcases p4351_3 (m.d 0 2) (by simp) with h4355 | h4355
                                      · rcases p4351_3 (m.d 1 2) (by simp) with h4356 | h4356
                                        · rcases p4351_3 (m.d 2 3) (by simp) with h4357 | h4357
                                          · linarith only [h3773, h4357, hlam]
                                          · linarith only [h4286, h4357, hlam]
                                        · linarith only [h4282, h4356, hlam]
                                      · linarith only [h4355, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      rcases p4351_3 (m.d 0 2) (by simp) with h4362 | h4362
                                      · rcases p4351_3 (m.d 1 2) (by simp) with h4363 | h4363
                                        · rcases p4351_3 (m.d 2 3) (by simp) with h4364 | h4364
                                          · linarith only [h3773, h4364, hlam]
                                          · linarith only [h4287, h4364, hlam]
                                        · linarith only [h4283, h4363, hlam]
                                      · linarith only [h4362, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h3773, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4292_1, p4351_1]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h4287, h4290, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4351_1, u3ehi3]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      rcases p4351_3 (m.d 0 2) (by simp) with h4372 | h4372
                                      · linarith only [h0, h4372, hlam]
                                      · linarith only [h3774, h4372, hlam]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      rcases p4351_3 (m.d 0 2) (by simp) with h4375 | h4375
                                      · linarith only [h0, h4375, hlam]
                                      · linarith only [h3775, h4375, hlam]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h3773, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h4281, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h3773, h4286, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p4351_1, u3ehi3]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h0, h3773, h4287, h4290, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4351_1, u3ehi3]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h3774, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h4282, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h4286, hlam, p4351_1]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h4288, hlam, p4351_1]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h3775, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h4283, hlam, p4351_0]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h4287, hlam, p4351_1]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [h0, h3775, h4286, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4351_1, u3ehi3]
                                    · have p4351_0 := h4351c.1
                                      have p4351_1 := h4351c.2.1
                                      have p4351_2 := h4351c.2.2.1
                                      have p4351_3 := h4351c.2.2.2
                                      linarith only [hlam, p4351_0]
                              · linarith only [h3777, h4346, hlam]
                            · linarith only [h3775, h4345, hlam]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3778, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4292_1]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3774, hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3776, hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3778, hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          rcases p4292_3 (m.d 0 1) (by simp) with h4400 | h4400
                          · linarith only [h3617, h4400, hlam]
                          · rcases p4292_3 (m.d 0 2) (by simp) with h4402 | h4402
                            · rcases p4292_3 (m.d 0 3) (by simp) with h4403 | h4403
                              · rcases p4292_3 (m.d 0 4) (by simp) with h4404 | h4404
                                · linarith only [h3778, h4404, hlam]
                                · linarith only [h3354, h4404, hlam]
                              · linarith only [h3129, h4403, hlam]
                            · linarith only [h0, h4402, hlam]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3775, hlam, p4292_1]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3777, hlam, p4292_0]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [h3774, h3778, h4286, hc45, hlam, hphi, ht34, p4292_1, u3ehi3]
                        · have p4292_0 := h4292c.1
                          have p4292_1 := h4292c.2.1
                          have p4292_2 := h4292c.2.2.1
                          have p4292_3 := h4292c.2.2.2
                          linarith only [hlam, p4292_0]
                  · linarith only [h4286, h4287, hc35, hlam, hphi, u3ehi3]
                · linarith only [h3776, h3778, h4286, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h3129, h3777, h4285, hlam]
            · linarith only [h3776, h3778, h4284, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h3775, h4283, hlam]
        · linarith only [h0, h3774, h4282, hlam]
      · linarith only [h0, h3773, h4281, hlam]
  · linarith only [h3776, h3777, hc35, hlam, hphi, u3ehi3]

end R2N4
