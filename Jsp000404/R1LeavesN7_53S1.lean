import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h856 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h857 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h858 | h858
  · rcases m.htr 0 4 5 (by decide) (by decide) with h859 | h859
    · rcases m.htr 1 2 3 (by decide) (by decide) with h860 | h860
      · rcases m.htr 1 2 4 (by decide) (by decide) with h861 | h861
        · rcases m.htr 1 2 5 (by decide) (by decide) with h862 | h862
          · rcases m.htr 1 3 4 (by decide) (by decide) with h863 | h863
            · rcases m.htr 1 3 5 (by decide) (by decide) with h864 | h864
              · rcases m.htr 1 4 5 (by decide) (by decide) with h865 | h865
                · rcases m.htr 2 3 4 (by decide) (by decide) with h866 | h866
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h867 | h867
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h868 | h868
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h869 | h869
                        · rcases h0emax with h870 | h870 | h870 | h870 | h870
                          · rcases h5bigk with h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h674, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h859, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi4]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h858, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p871_1, u3ehi4]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              rcases p871_3 (m.d 0 5) (by simp) with h876 | h876
                              · rcases p871_3 (m.d 1 5) (by simp) with h877 | h877
                                · rcases p871_3 (m.d 2 5) (by simp) with h878 | h878
                                  · linarith only [h856, h878, hlam]
                                  · linarith only [h868, h878, hlam]
                                · linarith only [h865, h877, hlam]
                              · linarith only [h859, h876, hlam]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h674, h865, hc01, hc14, hlam, hphi, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h861, h865, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi4]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p871_1, u3ehi4]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              rcases p871_3 (m.d 0 5) (by simp) with h887 | h887
                              · linarith only [h674, h887, hlam]
                              · linarith only [h859, h887, hlam]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h856, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h862, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p871_1, u3ehi4]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h855, h866, h868, hc02, hc45, hlam, hphi, ht0b, ht5b, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h858, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h864, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h867, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h855, h857, h869, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h859, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h865, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h868, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h869, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                          · linarith only [h855, h870, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h855, h866, h869, h870, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases h5bigk with h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c | h907c
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h674, hlam, p907_1]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h859, h870, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p907_1, u2ehi4]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h859, h870, hlam, hphi, ht0b, ht34, ht45, ht5b, p907_1, u3ehi4]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h859, h870, hc45, hlam, hphi, ht0b, ht5b, p907_1]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h674, h860, h863, h865, hc01, hc12, hlam, hphi, p907_1]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p907_1, u2ehi4]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p907_1, u3ehi4]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              rcases p907_3 (m.d 0 5) (by simp) with h917 | h917
                              · linarith only [h674, h917, hlam]
                              · linarith only [h859, h917, hlam]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h856, hlam, p907_1]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h862, hlam, p907_1]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p907_1, u3ehi4]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h856, h859, h870, hc45, hlam, hphi, ht0b, ht5b, p907_1]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h858, hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h864, hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h867, hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h855, h866, h869, hc03, hc45, hlam, hphi, ht0b, ht5b, p907_1]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h859, hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h865, hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h868, hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [h869, hlam, p907_0]
                            · have p907_0 := h907c.1
                              have p907_1 := h907c.2.1
                              have p907_2 := h907c.2.2.1
                              have p907_3 := h907c.2.2.2
                              linarith only [hlam, p907_0]
                          · rcases h5bigk with h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c | h935c
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h674, hlam, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h859, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p935_1, u2ehi4]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h674, h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p935_1, u3ehi4]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h870, hc45, hlam, hphi, ht0b, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h674, h860, h863, h865, hc01, hc12, hlam, hphi, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p935_1, u2ehi4]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p935_1, u3ehi4]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              rcases p935_3 (m.d 0 5) (by simp) with h945 | h945
                              · linarith only [h674, h945, hlam]
                              · linarith only [h859, h945, hlam]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h856, hlam, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h862, hlam, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p935_1, u3ehi4]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h0, h855, h866, h868, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h858, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h864, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h867, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h482, h858, h860, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p935_1]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h859, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h865, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h868, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [h869, hlam, p935_0]
                            · have p935_0 := h935c.1
                              have p935_1 := h935c.2.1
                              have p935_2 := h935c.2.2.1
                              have p935_3 := h935c.2.2.2
                              linarith only [hlam, p935_0]
                        · linarith only [h0, h855, h866, h868, h869, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h964 | h964
                        · linarith only [h868, h964, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases h0emax with h966 | h966 | h966 | h966 | h966
                          · rcases h5bigk with h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h674, hlam, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h674, h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p967_1, u2ehi4]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h674, h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p967_1, u3ehi4]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h674, h860, h863, h865, h868, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h674, h860, h863, h865, hc01, hc12, hlam, hphi, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p967_1, u2ehi4]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p967_1, u3ehi4]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h860, h863, h865, h868, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p967_1, u2ehi3]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h856, hlam, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h862, hlam, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p967_1, u3ehi4]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h868, hlam, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h858, hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h864, hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h867, hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h964, hlam, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h859, hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h865, hlam, p967_0]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h482, h857, h859, h860, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p967_1]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [h482, h857, h859, h860, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p967_1, u3ehi4]
                            · have p967_0 := h967c.1
                              have p967_1 := h967c.2.1
                              have p967_2 := h967c.2.2.1
                              have p967_3 := h967c.2.2.2
                              linarith only [hlam, p967_0]
                          · linarith only [h855, h966, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h855, h867, h964, h966, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h859, h868, h966, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h859, h868, h966, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h855, h858, h866, h867, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h998 | h998
                    · linarith only [h866, h998, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1000 | h1000
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1001 | h1001
                        · rcases h0emax with h1002 | h1002 | h1002 | h1002 | h1002
                          · rcases h5bigk with h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h674, hlam, p1003_1]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h859, h998, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1003_1, u3ehi2]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h674, h860, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1003_1, u3ehi4]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              rcases p1003_3 (m.d 0 5) (by simp) with h1008 | h1008
                              · rcases p1003_3 (m.d 1 5) (by simp) with h1009 | h1009
                                · rcases p1003_3 (m.d 2 5) (by simp) with h1010 | h1010
                                  · linarith only [h1010, h856, hlam]
                                  · linarith only [h1000, h1010, hlam]
                                · linarith only [h1009, h865, hlam]
                              · linarith only [h1008, h859, hlam]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h674, h860, h863, h865, hc01, hc12, hlam, hphi, p1003_1]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h860, h863, h865, h998, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1003_1, u2ehi2]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h860, h863, h865, h998, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1003_1, u2ehi2]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              rcases p1003_3 (m.d 0 5) (by simp) with h1019 | h1019
                              · linarith only [h1019, h674, hlam]
                              · linarith only [h1019, h859, hlam]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h856, hlam, p1003_1]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h862, hlam, p1003_1]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h998, hlam, p1003_1]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h0, h856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1003_1]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h858, hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h864, hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [hc35, hlam, hphi, ht23, p1003_1, u2ehi4]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h0, h1001, h855, h857, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1003_1]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h859, hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h865, hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h1000, hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [h1001, hlam, p1003_0]
                            · have p1003_0 := h1003c.1
                              have p1003_1 := h1003c.2.1
                              have p1003_2 := h1003c.2.2.1
                              have p1003_3 := h1003c.2.2.2
                              linarith only [hlam, p1003_0]
                          · linarith only [h1001, h1002, h855, h857, h998, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1001, h1002, h857, h998, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1001, h1002, h857, h998, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1002, h858, h998, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h1001, h855, h857, h859, h866, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1042 | h1042
                        · linarith only [h1000, h1042, h866, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h0, h1042, h855, h857, h859, h866, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h674, h859, h865, hlam]
              · linarith only [h482, h857, h864, hc35, hlam, hphi, u3ehi3]
            · linarith only [h482, h857, h863, hlam]
          · linarith only [h0, h855, h862, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h855, h861, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h855, h860, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1051 | h1051
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1052 | h1052
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1053 | h1053
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1054 | h1054
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1055 | h1055
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1056 | h1056
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1057 | h1057
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1058 | h1058
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1059 | h1059
                      · linarith only [h1057, h1059, h855, h857, h859, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1061 | h1061
                        · linarith only [h1059, h1061, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases h0emax with h1063 | h1063 | h1063 | h1063 | h1063
                          · rcases h5bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h674, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1051, h1054, h1056, h859, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1051, h1054, h1056, h859, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h859, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h674, hc01, hc15, hlam, hphi, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1053, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u2ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1051, h1055, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1051, h1054, h1056, h1059, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1064_1, u2ehi3]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h856, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1053, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1059, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h858, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1055, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1058, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1061, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1056, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1051, h1054, h1056, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1051, h1054, h1056, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi4]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                          · linarith only [h1063, h855, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h1058, h1061, h1063, h855, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases h5bigk with h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c | h1092c
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h674, hlam, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, h1059, h859, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1092_1, u2ehi3]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, h1061, h859, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h859, hlam, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, h674, hc01, hc12, hlam, hphi, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, h1059, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1092_1, u2ehi3]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, h1061, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, h859, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h856, hlam, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1053, hlam, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1061, h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1092_1, u3ehi3]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1059, hlam, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h858, hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1055, hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1058, hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1061, hlam, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1056, hlam, p1092_0]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [h1051, h1054, h1056, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1092_1]
                            · have p1092_0 := h1092c.1
                              have p1092_1 := h1092c.2.1
                              have p1092_2 := h1092c.2.2.1
                              have p1092_3 := h1092c.2.2.2
                              linarith only [hlam, p1092_0]
                          · rcases h5bigk with h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h674, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1059, h1063, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1118_1, u2ehi3]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1061, h1063, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1, u3ehi3]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h859, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, h1054, h1056, h674, hc01, hc12, hlam, hphi, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, h1054, h1056, h1059, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1118_1, u2ehi3]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, h1054, h1056, h1061, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1118_1, u3ehi3]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, h1054, h1056, h859, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h856, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1053, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1061, h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1, u3ehi3]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1059, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h858, hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1055, hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1058, hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1061, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1056, hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, h1054, h1056, h1058, h1061, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1118_1, u3ehi3]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, h1054, h1056, h1061, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1118_1, u3ehi3]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                    · linarith only [h1051, h1054, h1056, h1057, h1058, h858, h859, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1051, h1054, h1056, h1057, h857, h859, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1146 | h1146
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1147 | h1147
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1148 | h1148
                      · linarith only [h1052, h1056, h1148, h674, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1150 | h1150
                        · linarith only [h1052, h1056, h1150, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases h0emax with h1152 | h1152 | h1152 | h1152 | h1152
                          · rcases h5bigk with h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c | h1153c
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [hlam, p1153_0]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h674, hlam, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1148, h674, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1153_1, u2ehi3]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1051, h482, h858, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1153_1, u3ehi4]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h859, hlam, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h674, hc01, hc15, hlam, hphi, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [hlam, p1153_0]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1053, h1148, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1153_1, u2ehi3]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1051, h1055, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1153_1, u3ehi4]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1056, hlam, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h856, hlam, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1053, hlam, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [hlam, p1153_0]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1153_1, u3ehi4]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1148, hlam, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h858, hlam, p1153_0]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1055, hlam, p1153_0]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1147, hlam, p1153_0]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [hlam, p1153_0]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h1150, hlam, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1153_1]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p1153_1, u2ehi4]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [hc45, hlam, hphi, ht34, p1153_1, u3ehi4]
                            · have p1153_0 := h1153c.1
                              have p1153_1 := h1153c.2.1
                              have p1153_2 := h1153c.2.2.1
                              have p1153_3 := h1153c.2.2.2
                              linarith only [hlam, p1153_0]
                          · linarith only [h1147, h1150, h1152, h855, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1147, h1150, h1152, h855, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases h5bigk with h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [hlam, p1181_0]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h674, hlam, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1148, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1181_1, u2ehi3]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1150, h858, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi3]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h859, hlam, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h674, hc01, hc15, hlam, hphi, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [hlam, p1181_0]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1053, h1148, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1181_1, u2ehi3]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1051, h1055, h1150, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi3]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1056, hlam, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h856, hlam, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1053, hlam, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [hlam, p1181_0]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1150, h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi3]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1148, hlam, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h858, hlam, p1181_0]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1055, hlam, p1181_0]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1147, hlam, p1181_0]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [hlam, p1181_0]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1150, hlam, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1181_1]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p1181_1, u2ehi4]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [h1150, hc45, hlam, hphi, ht34, p1181_1, u3ehi3]
                            · have p1181_0 := h1181c.1
                              have p1181_1 := h1181c.2.1
                              have p1181_2 := h1181c.2.2.1
                              have p1181_3 := h1181c.2.2.2
                              linarith only [hlam, p1181_0]
                          · rcases h5bigk with h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h674, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1147, h1150, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi3]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1150, h858, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi3]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h859, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h674, hc01, hc15, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1053, h1147, h1150, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi3]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1051, h1055, h1150, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi3]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1056, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h856, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1053, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1150, h856, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi3]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1148, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h858, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1055, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1147, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1150, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h674, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h0, h1147, h1150, h674, h855, hc01, hc12, hc45, hlam, hphi, ht34, p1207_1, u3ehi3]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hc45, hlam, hphi, ht23, ht34, p1207_1, u2ehi4]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1150, hc45, hlam, hphi, ht34, p1207_1, u3ehi3]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                    · linarith only [h1051, h1146, h1147, h482, h858, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1146, h857, h859, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h1055, h482, h858, hlam]
            · linarith only [h1054, h482, h857, h859, hc45, hlam, hphi, ht34, u3ehi0]
          · linarith only [h0, h1053, h855, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1052, h855, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1051, h855, hlam]
  · linarith only [h857, h858, hc35, hlam, hphi, u3ehi3]

end R2N4
