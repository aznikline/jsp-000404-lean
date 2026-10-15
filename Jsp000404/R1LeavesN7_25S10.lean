import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4683 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4684 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4685 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 2 3 5 (by decide) (by decide) with h5126 | h5126
  · rcases m.htr 2 4 5 (by decide) (by decide) with h5127 | h5127
    · rcases m.htr 3 4 5 (by decide) (by decide) with h5128 | h5128
      · rcases h2bigk with h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c | h5129c
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h0, hlam, p5129_1]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          rcases p5129_3 (m.d 0 2) (by simp) with h5132 | h5132
          · rcases p5129_3 (m.d 1 2) (by simp) with h5133 | h5133
            · rcases p5129_3 (m.d 2 3) (by simp) with h5134 | h5134
              · linarith only [h5134, hlam, p5129_0]
              · rcases p5129_3 (m.d 2 4) (by simp) with h5136 | h5136
                · linarith only [h4676, h5136, hlam]
                · linarith only [h4685, h5136, hlam]
            · linarith only [h4680, h5133, hlam]
          · linarith only [h5132, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          rcases p5129_3 (m.d 0 2) (by simp) with h5141 | h5141
          · rcases p5129_3 (m.d 1 2) (by simp) with h5142 | h5142
            · rcases p5129_3 (m.d 2 3) (by simp) with h5143 | h5143
              · linarith only [h4675, h5143, hlam]
              · rcases p5129_3 (m.d 2 4) (by simp) with h5145 | h5145
                · linarith only [h5145, hlam, p5129_0]
                · rcases p5129_3 (m.d 2 5) (by simp) with h5147 | h5147
                  · linarith only [h4677, h5147, hlam]
                  · rcases h3bigk with h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c | h5149c
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h3871, hlam, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h0, h4675, h5126, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h0, h4675, h4685, h5126, h5128, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      rcases p5149_3 (m.d 0 3) (by simp) with h5154 | h5154
                      · rcases p5149_3 (m.d 1 3) (by simp) with h5155 | h5155
                        · rcases p5149_3 (m.d 2 3) (by simp) with h5156 | h5156
                          · linarith only [h4675, h5156, hlam]
                          · linarith only [h5126, h5156, hlam]
                        · linarith only [h4684, h5155, hlam]
                      · linarith only [h5154, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5149_1, u0ehi2]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4680, h5126, h5128, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4680, h4685, h5126, h5128, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      rcases p5149_3 (m.d 0 3) (by simp) with h5165 | h5165
                      · linarith only [h3871, h5165, hlam]
                      · linarith only [h4679, h5165, hlam]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4675, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4680, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4685, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4678, h4685, h5128, hc03, hc45, hlam, hphi, ht0b, ht5b, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4678, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4683, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4678, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h3871, h4678, h4680, h5128, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5149_1]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4679, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h4684, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h5126, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [h5128, hlam, p5149_0]
                    · have p5149_0 := h5149c.1
                      have p5149_1 := h5149c.2.1
                      have p5149_2 := h5149c.2.2.1
                      have p5149_3 := h5149c.2.2.2
                      linarith only [hlam, p5149_0]
            · linarith only [h4681, h5142, hlam]
          · linarith only [h5141, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          rcases p5129_3 (m.d 0 2) (by simp) with h5185 | h5185
          · rcases p5129_3 (m.d 1 2) (by simp) with h5186 | h5186
            · rcases p5129_3 (m.d 2 3) (by simp) with h5187 | h5187
              · linarith only [h4675, h5187, hlam]
              · linarith only [h5126, h5187, hlam]
            · linarith only [h4682, h5186, hlam]
          · linarith only [h5185, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p5129_1, u0ehi1]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          rcases p5129_3 (m.d 0 2) (by simp) with h5194 | h5194
          · linarith only [h0, h5194, hlam]
          · linarith only [h4675, h5194, hlam]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          rcases p5129_3 (m.d 0 2) (by simp) with h5197 | h5197
          · linarith only [h0, h5197, hlam]
          · linarith only [h4676, h5197, hlam]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          rcases p5129_3 (m.d 0 2) (by simp) with h5200 | h5200
          · linarith only [h0, h5200, hlam]
          · linarith only [h4677, h5200, hlam]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h4675, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h4680, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h4685, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h3871, h4678, h4680, h4685, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5129_1]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h4676, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h4681, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h3871, h4678, h4680, h4685, h5126, h5128, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5129_1]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          rcases p5129_3 (m.d 0 2) (by simp) with h5212 | h5212
          · rcases p5129_3 (m.d 1 2) (by simp) with h5213 | h5213
            · rcases p5129_3 (m.d 2 3) (by simp) with h5214 | h5214
              · linarith only [h4685, h5214, hlam]
              · linarith only [h5126, h5214, hlam]
            · linarith only [h4682, h5213, hlam]
          · linarith only [h4677, h5212, hlam]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h4677, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h4682, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h5126, hlam, p5129_1]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [h5127, hlam, p5129_0]
        · have p5129_0 := h5129c.1
          have p5129_1 := h5129c.2.1
          have p5129_2 := h5129c.2.2.1
          have p5129_3 := h5129c.2.2.2
          linarith only [hlam, p5129_0]
      · linarith only [h4685, h5127, h5128, hlam]
    · linarith only [h4685, h5126, h5127, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h5226 | h5226
    · rcases m.htr 3 4 5 (by decide) (by decide) with h5227 | h5227
      · rcases h2bigk with h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c | h5228c
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h0, hlam, p5228_1]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5231 | h5231
          · rcases p5228_3 (m.d 1 2) (by simp) with h5232 | h5232
            · rcases p5228_3 (m.d 2 3) (by simp) with h5233 | h5233
              · linarith only [h5233, hlam, p5228_0]
              · rcases p5228_3 (m.d 2 4) (by simp) with h5235 | h5235
                · linarith only [h4676, h5235, hlam]
                · linarith only [h4685, h5235, hlam]
            · linarith only [h4680, h5232, hlam]
          · linarith only [h5231, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5240 | h5240
          · rcases p5228_3 (m.d 1 2) (by simp) with h5241 | h5241
            · rcases p5228_3 (m.d 2 3) (by simp) with h5242 | h5242
              · linarith only [h4675, h5242, hlam]
              · rcases p5228_3 (m.d 2 4) (by simp) with h5244 | h5244
                · linarith only [h5244, hlam, p5228_0]
                · rcases p5228_3 (m.d 2 5) (by simp) with h5246 | h5246
                  · linarith only [h4677, h5246, hlam]
                  · rcases h3bigk with h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c | h5248c
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h3871, hlam, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      rcases p5248_3 (m.d 0 3) (by simp) with h5251 | h5251
                      · rcases p5248_3 (m.d 1 3) (by simp) with h5252 | h5252
                        · rcases p5248_3 (m.d 2 3) (by simp) with h5253 | h5253
                          · linarith only [h4675, h5253, hlam]
                          · rcases p5248_3 (m.d 3 4) (by simp) with h5255 | h5255
                            · linarith only [h4678, h5255, hlam]
                            · linarith only [h4685, h5255, hlam]
                        · linarith only [h4680, h5252, hlam]
                      · linarith only [h4675, h5251, hlam]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h3871, h4680, h4685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h3871, h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5248_1, u0ehi2]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      rcases p5248_3 (m.d 0 3) (by simp) with h5264 | h5264
                      · linarith only [h3871, h5264, hlam]
                      · linarith only [h4675, h5264, hlam]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4680, h5126, h5227, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4675, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4680, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4685, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h5126, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4678, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4683, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4678, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h3871, h4678, h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4679, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h4684, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p5248_1]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [h5227, hlam, p5248_0]
                    · have p5248_0 := h5248c.1
                      have p5248_1 := h5248c.2.1
                      have p5248_2 := h5248c.2.2.1
                      have p5248_3 := h5248c.2.2.2
                      linarith only [hlam, p5248_0]
            · linarith only [h4681, h5241, hlam]
          · linarith only [h5240, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5286 | h5286
          · rcases p5228_3 (m.d 1 2) (by simp) with h5287 | h5287
            · rcases p5228_3 (m.d 2 3) (by simp) with h5288 | h5288
              · linarith only [h4675, h5288, hlam]
              · rcases p5228_3 (m.d 2 4) (by simp) with h5290 | h5290
                · linarith only [h4676, h5290, hlam]
                · linarith only [h5226, h5290, hlam]
            · linarith only [h4682, h5287, hlam]
          · linarith only [h5286, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p5228_1, u0ehi1]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5297 | h5297
          · linarith only [h0, h5297, hlam]
          · linarith only [h4675, h5297, hlam]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5300 | h5300
          · linarith only [h0, h5300, hlam]
          · linarith only [h4676, h5300, hlam]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5303 | h5303
          · linarith only [h0, h5303, hlam]
          · linarith only [h4677, h5303, hlam]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h4675, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h4680, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h4685, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h5126, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h4676, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h4681, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5313 | h5313
          · rcases p5228_3 (m.d 1 2) (by simp) with h5314 | h5314
            · rcases p5228_3 (m.d 2 3) (by simp) with h5315 | h5315
              · linarith only [h4685, h5315, hlam]
              · rcases p5228_3 (m.d 2 4) (by simp) with h5317 | h5317
                · rcases p5228_3 (m.d 2 5) (by simp) with h5318 | h5318
                  · linarith only [h5226, h5318, hlam]
                  · linarith only [h5126, h5318, hlam]
                · linarith only [h4685, h5317, hlam]
            · linarith only [h4680, h5314, hlam]
          · linarith only [h4675, h5313, hlam]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5325 | h5325
          · rcases p5228_3 (m.d 1 2) (by simp) with h5326 | h5326
            · rcases p5228_3 (m.d 2 3) (by simp) with h5327 | h5327
              · linarith only [h4685, h5327, hlam]
              · rcases p5228_3 (m.d 2 4) (by simp) with h5329 | h5329
                · rcases p5228_3 (m.d 2 5) (by simp) with h5330 | h5330
                  · linarith only [h5226, h5330, hlam]
                  · rcases h3bigk with h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h3871, hlam, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      rcases p5332_3 (m.d 0 3) (by simp) with h5335 | h5335
                      · rcases p5332_3 (m.d 1 3) (by simp) with h5336 | h5336
                        · rcases p5332_3 (m.d 2 3) (by simp) with h5337 | h5337
                          · linarith only [h4675, h5337, hlam]
                          · rcases p5332_3 (m.d 3 4) (by simp) with h5339 | h5339
                            · linarith only [h4678, h5339, hlam]
                            · linarith only [h4685, h5339, hlam]
                        · linarith only [h4680, h5336, hlam]
                      · linarith only [h4675, h5335, hlam]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h3871, h4680, h4685, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5228_1, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h3871, h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5332_1, u0ehi2]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      rcases p5332_3 (m.d 0 3) (by simp) with h5348 | h5348
                      · linarith only [h3871, h5348, hlam]
                      · linarith only [h4675, h5348, hlam]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4680, h4685, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5228_1, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4675, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4680, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4685, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h5126, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4678, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4683, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4678, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h3871, h4678, h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4679, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h4684, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p5332_1]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [h5227, hlam, p5332_0]
                    · have p5332_0 := h5332c.1
                      have p5332_1 := h5332c.2.1
                      have p5332_2 := h5332c.2.2.1
                      have p5332_3 := h5332c.2.2.2
                      linarith only [hlam, p5332_0]
                · linarith only [h5226, h5329, hlam]
            · linarith only [h4682, h5326, hlam]
          · linarith only [h4677, h5325, hlam]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h4677, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h4682, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          rcases p5228_3 (m.d 0 2) (by simp) with h5373 | h5373
          · rcases p5228_3 (m.d 1 2) (by simp) with h5374 | h5374
            · rcases p5228_3 (m.d 2 3) (by simp) with h5375 | h5375
              · linarith only [h5126, h5375, hlam]
              · rcases p5228_3 (m.d 2 4) (by simp) with h5377 | h5377
                · rcases p5228_3 (m.d 2 5) (by simp) with h5378 | h5378
                  · rcases h3bigk with h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c | h5379c
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h3871, hlam, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      rcases p5379_3 (m.d 0 3) (by simp) with h5382 | h5382
                      · rcases p5379_3 (m.d 1 3) (by simp) with h5383 | h5383
                        · rcases p5379_3 (m.d 2 3) (by simp) with h5384 | h5384
                          · linarith only [h4675, h5384, hlam]
                          · rcases p5379_3 (m.d 3 4) (by simp) with h5386 | h5386
                            · linarith only [h4678, h5386, hlam]
                            · linarith only [h4685, h5386, hlam]
                        · linarith only [h4680, h5383, hlam]
                      · linarith only [h4675, h5382, hlam]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h3871, h4680, h4685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h3871, h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5379_1, u0ehi2]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      rcases p5379_3 (m.d 0 3) (by simp) with h5395 | h5395
                      · linarith only [h3871, h5395, hlam]
                      · linarith only [h4675, h5395, hlam]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4680, h4685, h5226, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5228_1, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5228_1, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4675, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4680, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4685, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h5126, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4678, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4683, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4678, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h3871, h4678, h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5228_1, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4679, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h4684, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p5379_1]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [h5227, hlam, p5379_0]
                    · have p5379_0 := h5379c.1
                      have p5379_1 := h5379c.2.1
                      have p5379_2 := h5379c.2.2.1
                      have p5379_3 := h5379c.2.2.2
                      linarith only [hlam, p5379_0]
                  · linarith only [h5126, h5378, hlam]
                · linarith only [h4685, h5377, hlam]
            · linarith only [h4680, h5374, hlam]
          · linarith only [h4675, h5373, hlam]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [h5226, hlam, p5228_0]
        · have p5228_0 := h5228c.1
          have p5228_1 := h5228c.2.1
          have p5228_2 := h5228c.2.2.1
          have p5228_3 := h5228c.2.2.2
          linarith only [hlam, p5228_0]
      · linarith only [h4685, h5226, h5227, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h5422 | h5422
      · rcases h2bigk with h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c | h5423c
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h0, hlam, p5423_1]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4675, h4678, h4685, h5226, h5422, hlam, p5423_2]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4675, h4678, h5226, h5422, hlam, p5423_2]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          rcases p5423_3 (m.d 0 2) (by simp) with h5428 | h5428
          · rcases p5423_3 (m.d 1 2) (by simp) with h5429 | h5429
            · rcases p5423_3 (m.d 2 3) (by simp) with h5430 | h5430
              · linarith only [h4675, h5430, hlam]
              · rcases p5423_3 (m.d 2 4) (by simp) with h5432 | h5432
                · linarith only [h4676, h5432, hlam]
                · rcases p5423_3 (m.d 2 5) (by simp) with h5434 | h5434
                  · linarith only [h5434, hlam, p5423_0]
                  · rcases h3bigk with h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c | h5436c
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h3871, hlam, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      rcases p5436_3 (m.d 0 3) (by simp) with h5439 | h5439
                      · rcases p5436_3 (m.d 1 3) (by simp) with h5440 | h5440
                        · rcases p5436_3 (m.d 2 3) (by simp) with h5441 | h5441
                          · linarith only [h4675, h5441, hlam]
                          · rcases p5436_3 (m.d 3 4) (by simp) with h5443 | h5443
                            · linarith only [h4678, h5443, hlam]
                            · linarith only [h4685, h5443, hlam]
                        · linarith only [h4680, h5440, hlam]
                      · linarith only [h4675, h5439, hlam]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4675, h4685, h5226, h5422, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h0, h4675, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5436_1, u0ehi2]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      rcases p5436_3 (m.d 0 3) (by simp) with h5452 | h5452
                      · linarith only [h3871, h5452, hlam]
                      · linarith only [h4675, h5452, hlam]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4680, h4685, h5226, h5422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4680, h4685, h5226, h5422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4675, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4680, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4685, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h5126, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4678, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4683, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4678, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h3871, h4678, h4680, h4685, h5226, h5422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4679, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h4684, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p5436_1]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [h5422, hlam, p5436_0]
                    · have p5436_0 := h5436c.1
                      have p5436_1 := h5436c.2.1
                      have p5436_2 := h5436c.2.2.1
                      have p5436_3 := h5436c.2.2.2
                      linarith only [hlam, p5436_0]
            · linarith only [h4682, h5429, hlam]
          · linarith only [h5428, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p5423_1, u0ehi1]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h3871, h4678, h4680, h4685, h5226, h5422, hlam, p5423_2]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h3871, h4678, h4680, h5226, h5422, hlam, p5423_2]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          rcases p5423_3 (m.d 0 2) (by simp) with h5478 | h5478
          · linarith only [h0, h5478, hlam]
          · linarith only [h4677, h5478, hlam]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4675, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4680, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4685, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h5126, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4676, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4681, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h3871, h4678, h4680, h5226, h5422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5423_1]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h5226, hlam, p5423_1]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4677, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h4682, hlam, p5423_0]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h3871, h4678, h4680, h5226, h5422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5423_1]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [h3871, h4678, h4680, h5226, h5422, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5423_1]
        · have p5423_0 := h5423c.1
          have p5423_1 := h5423c.2.1
          have p5423_2 := h5423c.2.2.1
          have p5423_3 := h5423c.2.2.2
          linarith only [hlam, p5423_0]
      · rcases h2bigk with h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h0, hlam, p5496_1]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5499 | h5499
          · rcases p5496_3 (m.d 1 2) (by simp) with h5500 | h5500
            · rcases p5496_3 (m.d 2 3) (by simp) with h5501 | h5501
              · linarith only [h5501, hlam, p5496_0]
              · rcases p5496_3 (m.d 2 4) (by simp) with h5503 | h5503
                · linarith only [h4676, h5503, hlam]
                · linarith only [h4685, h5503, hlam]
            · linarith only [h4680, h5500, hlam]
          · linarith only [h5499, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5508 | h5508
          · rcases p5496_3 (m.d 1 2) (by simp) with h5509 | h5509
            · rcases p5496_3 (m.d 2 3) (by simp) with h5510 | h5510
              · linarith only [h4675, h5510, hlam]
              · rcases p5496_3 (m.d 2 4) (by simp) with h5512 | h5512
                · linarith only [h5512, hlam, p5496_0]
                · rcases p5496_3 (m.d 2 5) (by simp) with h5514 | h5514
                  · linarith only [h4677, h5514, hlam]
                  · linarith only [h5226, h5514, hlam]
            · linarith only [h4681, h5509, hlam]
          · linarith only [h5508, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5519 | h5519
          · rcases p5496_3 (m.d 1 2) (by simp) with h5520 | h5520
            · rcases p5496_3 (m.d 2 3) (by simp) with h5521 | h5521
              · linarith only [h4675, h5521, hlam]
              · rcases p5496_3 (m.d 2 4) (by simp) with h5523 | h5523
                · linarith only [h4676, h5523, hlam]
                · rcases p5496_3 (m.d 2 5) (by simp) with h5525 | h5525
                  · linarith only [h5525, hlam, p5496_0]
                  · rcases h3bigk with h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c | h5527c
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h3871, hlam, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      rcases p5527_3 (m.d 0 3) (by simp) with h5530 | h5530
                      · rcases p5527_3 (m.d 1 3) (by simp) with h5531 | h5531
                        · rcases p5527_3 (m.d 2 3) (by simp) with h5532 | h5532
                          · linarith only [h4675, h5532, hlam]
                          · rcases p5527_3 (m.d 3 4) (by simp) with h5534 | h5534
                            · linarith only [h4678, h5534, hlam]
                            · linarith only [h4685, h5534, hlam]
                        · linarith only [h4680, h5531, hlam]
                      · linarith only [h4675, h5530, hlam]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h3871, h4680, h4685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h3871, h4680, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5527_1, u0ehi2]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      rcases p5527_3 (m.d 0 3) (by simp) with h5543 | h5543
                      · linarith only [h3871, h5543, hlam]
                      · linarith only [h4675, h5543, hlam]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4680, h4685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4680, h4685, h5422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4675, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4680, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4685, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h5126, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4678, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4683, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4679, h5422, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h5422, hlam, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4679, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h4684, hlam, p5527_0]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h3871, h4679, h4680, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [h3871, h4679, h4680, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5527_1]
                    · have p5527_0 := h5527c.1
                      have p5527_1 := h5527c.2.1
                      have p5527_2 := h5527c.2.2.1
                      have p5527_3 := h5527c.2.2.2
                      linarith only [hlam, p5527_0]
            · linarith only [h4682, h5520, hlam]
          · linarith only [h5519, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p5496_1, u0ehi1]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5567 | h5567
          · linarith only [h0, h5567, hlam]
          · linarith only [h4675, h5567, hlam]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5570 | h5570
          · linarith only [h0, h5570, hlam]
          · linarith only [h4676, h5570, hlam]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5573 | h5573
          · linarith only [h0, h5573, hlam]
          · linarith only [h4677, h5573, hlam]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h4675, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h4680, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h4685, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h5126, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h4676, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h4681, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h5226, hc23, hc45, hlam, hphi, ht34, p5496_1]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h5226, hlam, p5496_1]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h4677, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [h4682, hlam, p5496_0]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5588 | h5588
          · rcases p5496_3 (m.d 1 2) (by simp) with h5589 | h5589
            · rcases p5496_3 (m.d 2 3) (by simp) with h5590 | h5590
              · linarith only [h5126, h5590, hlam]
              · rcases p5496_3 (m.d 2 4) (by simp) with h5592 | h5592
                · linarith only [h5226, h5592, hlam]
                · linarith only [h4685, h5592, hlam]
            · linarith only [h4680, h5589, hlam]
          · linarith only [h4675, h5588, hlam]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          rcases p5496_3 (m.d 0 2) (by simp) with h5597 | h5597
          · rcases p5496_3 (m.d 1 2) (by simp) with h5598 | h5598
            · rcases p5496_3 (m.d 2 3) (by simp) with h5599 | h5599
              · linarith only [h5126, h5599, hlam]
              · rcases p5496_3 (m.d 2 4) (by simp) with h5601 | h5601
                · linarith only [h5226, h5601, hlam]
                · rcases p5496_3 (m.d 2 5) (by simp) with h5603 | h5603
                  · rcases h3bigk with h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c | h5604c
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h3871, hlam, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      rcases p5604_3 (m.d 0 3) (by simp) with h5607 | h5607
                      · rcases p5604_3 (m.d 1 3) (by simp) with h5608 | h5608
                        · rcases p5604_3 (m.d 2 3) (by simp) with h5609 | h5609
                          · linarith only [h4675, h5609, hlam]
                          · rcases p5604_3 (m.d 3 4) (by simp) with h5611 | h5611
                            · linarith only [h4678, h5611, hlam]
                            · linarith only [h4685, h5611, hlam]
                        · linarith only [h4680, h5608, hlam]
                      · linarith only [h4675, h5607, hlam]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4675, h4685, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h3871, h4680, h4685, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5496_1, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4680, hc12, hlam, hphi, ht01, p5604_1, u0ehi2]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      rcases p5604_3 (m.d 0 3) (by simp) with h5620 | h5620
                      · linarith only [h3871, h5620, hlam]
                      · linarith only [h4675, h5620, hlam]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4680, h4685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4680, h4685, h5126, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5496_1, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4675, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4680, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4685, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h5126, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4678, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4683, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [hc23, hc34, hlam, hphi, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h5422, hlam, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4679, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h4684, hlam, p5604_0]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [hc23, hc35, hlam, hphi, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [h3871, h4679, h4680, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5604_1]
                    · have p5604_0 := h5604c.1
                      have p5604_1 := h5604c.2.1
                      have p5604_2 := h5604c.2.2.1
                      have p5604_3 := h5604c.2.2.2
                      linarith only [hlam, p5604_0]
                  · linarith only [h5226, h5603, hlam]
            · linarith only [h4681, h5598, hlam]
          · linarith only [h4676, h5597, hlam]
        · have p5496_0 := h5496c.1
          have p5496_1 := h5496c.2.1
          have p5496_2 := h5496c.2.2.1
          have p5496_3 := h5496c.2.2.2
          linarith only [hlam, p5496_0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4683 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4684 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h4685 | h4685
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682 h4683 h4684 h4685
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682 h4683 h4684 h4685

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4683 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4684 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  linarith only [h3871, h4679, h4684, hlam]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4683 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h4684 | h4684
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682 h4683 h4684
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682 h4683 h4684

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4683 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  linarith only [h3871, h4683, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h4683 | h4683
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682 h4683
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682 h4683

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4682 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  linarith only [h0, h4682, hc25, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h4682 | h4682
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681 h4682

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4681 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  linarith only [h3871, h4680, h4681, hc24, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h4681 | h4681
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680 h4681

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4680 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  linarith only [h0, h4680, hc23, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h4680 | h4680
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679 h4680

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4679 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h5649 | h5649
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5650 | h5650
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5651 | h5651
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5652 | h5652
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5653 | h5653
          · linarith only [h3871, h4679, h5649, h5653, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h3871, h5653, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h3871, h4678, h5652, hc03, hlam, hphi, u0ehi0]
      · linarith only [h0, h4677, h5651, hc02, hlam, hphi, u0ehi0]
    · linarith only [h0, h5650, hc24, hlam, hphi, ht01, ht12, u0ehi0]
  · linarith only [h0, h4675, h5649, hc02, hlam, hphi, u0ehi0]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h4679 | h4679
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679
  · exact r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h3871 h4675 h4676 h4677 h4678 h4679

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3871 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4675 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4676 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4677 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4678 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h5660 | h5660
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5661 | h5661
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5662 | h5662
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5663 | h5663
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5664 | h5664
          · linarith only [h4678, h5664, hc13, hlam, hphi, ht01, u0ehi2]
          · linarith only [h3871, h5664, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h0, h4677, h5660, h5663, hc03, hlam, hphi, u0ehi0]
      · linarith only [h0, h5662, hc24, hlam, hphi, ht01, ht12, u0ehi0]
    · linarith only [h0, h4675, h5661, hc02, hlam, hphi, u0ehi0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5670 | h5670
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5671 | h5671
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5672 | h5672
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5673 | h5673
          · linarith only [h4678, h5673, hc13, hlam, hphi, ht01, u0ehi2]
          · linarith only [h3871, h5673, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h0, h5672, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h3871, h4676, h5670, h5671, hc02, hlam, hphi, u0ehi0]
    · linarith only [h0, h5670, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
