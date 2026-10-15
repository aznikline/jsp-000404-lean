import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3679 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3845 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3846 | h3846
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3847 | h3847
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3848 | h3848
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3849 | h3849
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3850 | h3850
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3851 | h3851
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3852 | h3852
              · rcases h0bigk with h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c | h3853c
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, hlam, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h2474, hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3236, hlam, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3679, hlam, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, h3849, hc12, hlam, hphi, ht01, ht0b, ht5b, p3853_1, u5ehi3]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, h3850, hc12, hlam, hphi, ht01, ht0b, ht5b, p3853_1, u5ehi4]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3853_1, u5ehi0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h2474, hc01, hc13, hlam, hphi, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3845, hlam, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, h3845, h3850, hc12, hlam, hphi, ht01, ht0b, ht5b, p3853_1, u5ehi4]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, h3845, h3847, hc12, hlam, hphi, ht01, ht0b, ht5b, p3853_1, u5ehi2]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3846, hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3848, hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h0, h3845, h3847, h3848, hc12, hlam, hphi, ht01, ht0b, ht5b, p3853_1, u5ehi2]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3847, hlam, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3849, hlam, p3853_0]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [h3850, hlam, p3853_1]
                · have p3853_0 := h3853c.1
                  have p3853_1 := h3853c.2.1
                  have p3853_2 := h3853c.2.2.1
                  have p3853_3 := h3853c.2.2.2
                  linarith only [hlam, p3853_0]
              · rcases h0bigk with h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c | h3879c
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h0, hlam, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h2474, hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3236, hlam, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3679, hlam, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h0, h3848, h3850, hc12, hlam, hphi, ht01, ht0b, ht5b, p3879_1, u5ehi0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h0, h3850, hc12, hlam, hphi, ht01, ht0b, ht5b, p3879_1, u5ehi0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3879_1, u5ehi0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h2474, h3851, hc01, hc12, hlam, hphi, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3845, hlam, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h2474, h3847, h3850, h3851, hc12, hlam, hphi, ht01, ht0b, ht5b, p3879_1, u5ehi2]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h2474, h3847, h3851, hc12, hlam, hphi, ht01, ht0b, ht5b, p3879_1, u5ehi2]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3846, hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3848, hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h2474, h3847, h3848, h3851, hc12, hlam, hphi, ht01, ht0b, ht5b, p3879_1, u5ehi2]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3847, hlam, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3849, hlam, p3879_0]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [h3850, hlam, p3879_1]
                · have p3879_0 := h3879c.1
                  have p3879_1 := h3879c.2.1
                  have p3879_2 := h3879c.2.2.1
                  have p3879_3 := h3879c.2.2.2
                  linarith only [hlam, p3879_0]
            · linarith only [h0, h3845, h3851, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3906 | h3906
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3907 | h3907
              · rcases h0bigk with h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c | h3908c
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h0, hlam, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h2474, hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3236, hlam, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3679, hlam, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h0, h2474, hc01, hc12, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h0, h3236, hc01, hc12, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3908_1, u5ehi0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h2474, hc01, hc13, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3845, hlam, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h0, h3236, h3845, hc01, hc12, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h0, h3845, h3847, hc12, hlam, hphi, ht01, ht0b, ht5b, p3908_1, u5ehi2]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3846, hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3848, hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3850, hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3847, hlam, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3849, hlam, p3908_0]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [h3850, hc04, hc45, hlam, hphi, p3908_1]
                · have p3908_0 := h3908c.1
                  have p3908_1 := h3908c.2.1
                  have p3908_2 := h3908c.2.2.1
                  have p3908_3 := h3908c.2.2.2
                  linarith only [hlam, p3908_0]
              · rcases h0bigk with h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c | h3934c
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h0, hlam, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h2474, hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3236, hlam, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3679, hlam, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h0, h2474, hc01, hc12, hlam, hphi, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h0, h3848, h3907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3934_1, u5ehi0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h2474, h3906, hc01, hc12, hlam, hphi, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3845, hlam, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h2474, h3848, h3906, h3907, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h2474, h3847, h3906, hc12, hlam, hphi, ht01, ht0b, ht5b, p3934_1, u5ehi2]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3846, hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3848, hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3850, hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3847, hlam, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3849, hlam, p3934_0]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [h3850, hc04, hc45, hlam, hphi, p3934_1]
                · have p3934_0 := h3934c.1
                  have p3934_1 := h3934c.2.1
                  have p3934_2 := h3934c.2.2.1
                  have p3934_3 := h3934c.2.2.2
                  linarith only [hlam, p3934_0]
            · linarith only [h0, h3845, h3906, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3961 | h3961
          · linarith only [h3848, h3849, h3961, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3963 | h3963
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3964 | h3964
              · rcases h0bigk with h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h0, hlam, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h2474, hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3236, hlam, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3679, hlam, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h0, h3845, h3964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h0, h3236, hc01, hc12, hlam, hphi, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3965_1, u5ehi0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h2474, hc01, hc13, hlam, hphi, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3845, hlam, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h0, h3236, h3845, hc01, hc12, hlam, hphi, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3849, hlam, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3961, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3846, hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3848, hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3961, hlam, p3965_0]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3847, hlam, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3849, hc03, hc35, hlam, hphi, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [h3961, hc04, hc45, hlam, hphi, p3965_1]
                · have p3965_0 := h3965c.1
                  have p3965_1 := h3965c.2.1
                  have p3965_2 := h3965c.2.2.1
                  have p3965_3 := h3965c.2.2.2
                  linarith only [hlam, p3965_0]
              · linarith only [h3848, h3849, h3964, hc23, hc35, hlam, hphi]
            · linarith only [h0, h3845, h3963, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3993 | h3993
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3994 | h3994
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3995 | h3995
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3996 | h3996
              · linarith only [h3845, h3848, h3993, h3996, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
              · rcases h0bigk with h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c | h3998c
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [hlam, p3998_0]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h0, hlam, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h2474, hlam, p3998_0]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3236, hlam, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3679, hlam, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [hlam, p3998_0]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h0, h3993, hc12, hlam, hphi, ht01, ht0b, ht5b, p3998_1, u5ehi3]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h0, h3848, h3993, hc12, hlam, hphi, ht01, ht0b, ht5b, p3998_1, u5ehi3]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h0, h3847, hc12, hlam, hphi, ht01, ht0b, ht5b, p3998_1, u5ehi2]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3848, hc01, hc34, hlam, hphi, ht12, ht23, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3845, hlam, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [hlam, p3998_0]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3848, hlam, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3847, h3848, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3998_1, u5ehi2]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3846, hlam, p3998_0]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3848, hc03, hc34, hlam, hphi, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [hlam, p3998_0]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3847, h3848, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3998_1, u5ehi2]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3847, hlam, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3993, hlam, p3998_0]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [h3994, hlam, p3998_1]
                · have p3998_0 := h3998c.1
                  have p3998_1 := h3998c.2.1
                  have p3998_2 := h3998c.2.2.1
                  have p3998_3 := h3998c.2.2.2
                  linarith only [hlam, p3998_0]
            · linarith only [h0, h3845, h3995, hlam]
          · linarith only [h3848, h3993, h3994, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4026 | h4026
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4027 | h4027
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4028 | h4028
              · linarith only [h3845, h3848, h4028, hlam]
              · rcases h0bigk with h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c | h4030c
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [hlam, p4030_0]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h0, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h2474, hlam, p4030_0]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3236, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3679, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [hlam, p4030_0]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h0, h2474, hc01, hc12, hlam, hphi, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h0, h4026, hc12, hlam, hphi, ht01, ht0b, ht5b, p4030_1, u5ehi4]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p4030_1, u5ehi0]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3848, hc01, hc34, hlam, hphi, ht12, ht23, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3845, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [hlam, p4030_0]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3848, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3993, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3846, hlam, p4030_0]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3848, hc03, hc34, hlam, hphi, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [hlam, p4030_0]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3847, h3848, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4030_1, u5ehi2]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h3847, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h2474, h3993, hc01, hc35, hlam, hphi, ht12, ht23, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [h4026, hlam, p4030_1]
                · have p4030_0 := h4030c.1
                  have p4030_1 := h4030c.2.1
                  have p4030_2 := h4030c.2.2.1
                  have p4030_3 := h4030c.2.2.2
                  linarith only [hlam, p4030_0]
            · linarith only [h0, h3845, h4027, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4057 | h4057
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4058 | h4058
              · linarith only [h3845, h3848, h4058, hlam]
              · rcases h0bigk with h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c | h4060c
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [hlam, p4060_0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h0, hlam, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h2474, hlam, p4060_0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3236, hlam, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3679, hlam, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [hlam, p4060_0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h0, h2474, hc01, hc12, hlam, hphi, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h0, h3236, hc01, hc12, hlam, hphi, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p4060_1, u5ehi0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3848, hc01, hc34, hlam, hphi, ht12, ht23, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3845, hlam, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [hlam, p4060_0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3848, hlam, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3993, hlam, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3846, hlam, p4060_0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3848, hc03, hc34, hlam, hphi, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [hlam, p4060_0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h4026, hlam, p4060_0]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h3847, hlam, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h2474, h3993, hc01, hc35, hlam, hphi, ht12, ht23, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [h4026, hc04, hc45, hlam, hphi, p4060_1]
                · have p4060_0 := h4060c.1
                  have p4060_1 := h4060c.2.1
                  have p4060_2 := h4060c.2.2.1
                  have p4060_3 := h4060c.2.2.2
                  linarith only [hlam, p4060_0]
            · linarith only [h0, h3845, h4057, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4087 | h4087
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4088 | h4088
        · linarith only [h3845, h3847, h4088, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4090 | h4090
          · linarith only [h3845, h3847, h4087, h4090, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4092 | h4092
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4093 | h4093
              · rcases h0bigk with h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c | h4094c
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h0, hlam, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h2474, hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3236, hlam, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3679, hlam, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3847, hc01, hc25, hlam, hphi, ht12, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3847, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3847, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3847, hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h2474, hc01, hc13, hlam, hphi, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3845, hlam, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3236, h3845, h3847, hc01, hc25, hlam, hphi, ht12, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h4088, hlam, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3846, hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h4087, hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h4090, hlam, p4094_0]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3847, hc02, hc25, hlam, hphi, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h4088, hc03, hc35, hlam, hphi, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [h3236, h4090, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4094_1]
                · have p4094_0 := h4094c.1
                  have p4094_1 := h4094c.2.1
                  have p4094_2 := h4094c.2.2.1
                  have p4094_3 := h4094c.2.2.2
                  linarith only [hlam, p4094_0]
              · linarith only [h4087, h4088, h4093, hc23, hc35, hlam, hphi]
            · linarith only [h0, h3845, h4092, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4122 | h4122
        · linarith only [h3846, h3847, h4087, h4122, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4124 | h4124
          · linarith only [h3846, h3847, h4124, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4126 | h4126
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4127 | h4127
              · linarith only [h3845, h3847, h4087, h4127, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases h0bigk with h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c | h4129c
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h0, hlam, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h2474, hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3236, hlam, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3679, hlam, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3847, hc01, hc25, hlam, hphi, ht12, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h2474, h3847, hc01, hc25, hlam, hphi, ht12, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3847, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3847, hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h2474, hc01, hc13, hlam, hphi, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3845, hlam, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h4087, hlam, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h4122, hlam, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h4087, hc01, hc34, hlam, hphi, ht12, ht23, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3846, hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h3846, h3847, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h4124, hlam, p4129_0]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h4122, hc01, hc35, hlam, hphi, ht12, ht23, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h4122, hc02, hc35, hlam, hphi, ht23, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h2474, h4122, hc01, hc35, hlam, hphi, ht12, ht23, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [h4124, hc04, hc45, hlam, hphi, p4129_1]
                · have p4129_0 := h4129c.1
                  have p4129_1 := h4129c.2.1
                  have p4129_2 := h4129c.2.2.1
                  have p4129_3 := h4129c.2.2.2
                  linarith only [hlam, p4129_0]
            · linarith only [h0, h3845, h4126, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4156 | h4156
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4157 | h4157
      · linarith only [h3845, h3846, h4157, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4159 | h4159
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4160 | h4160
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4161 | h4161
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4162 | h4162
              · linarith only [h3845, h3846, h4157, h4162, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases h0bigk with h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c | h4164c
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [hlam, p4164_0]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h0, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h2474, hlam, p4164_0]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3236, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3679, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3846, h4162, hc01, hc34, hlam, hphi, ht12, ht23, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [hlam, p4164_0]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3846, h4159, h4162, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4164_1, u5ehi3]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3846, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3846, h4156, h4162, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4164_1, u5ehi2]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h2474, h4161, hc01, hc12, hlam, hphi, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3845, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [hlam, p4164_0]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h4157, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3845, h3846, h4156, h4162, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4164_1, u5ehi2]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3846, h4162, hc02, hc34, hlam, hphi, ht23, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3846, h4162, hc03, hc34, hlam, hphi, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [hlam, p4164_0]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3846, h4156, h4162, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4164_1, u5ehi2]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h4156, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h4159, hlam, p4164_0]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [h4160, hlam, p4164_1]
                · have p4164_0 := h4164c.1
                  have p4164_1 := h4164c.2.1
                  have p4164_2 := h4164c.2.2.1
                  have p4164_3 := h4164c.2.2.2
                  linarith only [hlam, p4164_0]
            · linarith only [h0, h3845, h4161, hlam]
          · linarith only [h3845, h3846, h4159, h4160, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4192 | h4192
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4193 | h4193
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4194 | h4194
              · linarith only [h0, h2474, h3845, h4157, h4194, hc01, hc12, hlam, hphi]
              · rcases h0bigk with h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [hlam, p4196_0]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h0, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h2474, hlam, p4196_0]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3236, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3679, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3846, h4194, hc01, hc34, hlam, hphi, ht12, ht23, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [hlam, p4196_0]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h2474, h3846, h4194, hc01, hc34, hlam, hphi, ht12, ht23, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3846, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3846, h4194, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4196_1, u5ehi0]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h2474, hc01, hc13, hlam, hphi, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3845, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [hlam, p4196_0]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h4157, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h4159, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3846, h4194, hc01, hc34, hlam, hphi, ht12, ht23, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3846, h4194, hc02, hc34, hlam, hphi, ht23, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3846, h4194, hc03, hc34, hlam, hphi, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [hlam, p4196_0]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3846, h4192, h4194, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4196_1, u5ehi4]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h4156, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h2474, h3846, h4156, h4194, hc01, hc34, hlam, hphi, ht12, ht23, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [h4192, hlam, p4196_1]
                · have p4196_0 := h4196c.1
                  have p4196_1 := h4196c.2.1
                  have p4196_2 := h4196c.2.2.1
                  have p4196_3 := h4196c.2.2.2
                  linarith only [hlam, p4196_0]
            · linarith only [h0, h3845, h4193, hlam]
          · linarith only [h3846, h4156, h4192, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4224 | h4224
      · linarith only [h3845, h3846, h4224, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4226 | h4226
        · linarith only [h3845, h4156, h4226, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4228 | h4228
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4229 | h4229
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4230 | h4230
              · linarith only [h3845, h4156, h4224, h4230, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases h0bigk with h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c | h4232c
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [hlam, p4232_0]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h0, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h2474, hlam, p4232_0]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3236, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3679, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3846, h4230, hc01, hc34, hlam, hphi, ht12, ht23, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [hlam, p4232_0]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h2474, h3846, h4230, hc01, hc34, hlam, hphi, ht12, ht23, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3846, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h4156, hlam, p4232_0]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h2474, h4229, hc01, hc12, hlam, hphi, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3845, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [hlam, p4232_0]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h4224, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h4226, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3236, hc01, hc14, hlam, hphi, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3846, h4230, hc02, hc34, hlam, hphi, ht23, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3846, h4230, hc03, hc34, hlam, hphi, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [hlam, p4232_0]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3845, h3846, h4156, h4230, hc23, hc34, hlam, hphi, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h3845, h4156, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h2474, h4226, hc01, hc35, hlam, hphi, ht12, ht23, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [h4228, hlam, p4232_1]
                · have p4232_0 := h4232c.1
                  have p4232_1 := h4232c.2.1
                  have p4232_2 := h4232c.2.2.1
                  have p4232_3 := h4232c.2.2.2
                  linarith only [hlam, p4232_0]
            · linarith only [h0, h3845, h4229, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4259 | h4259
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4260 | h4260
              · linarith only [h3845, h3846, h4228, h4260, hc34, hc45, hlam, hphi]
              · rcases h0bigk with h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [hlam, p4262_0]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h0, hlam, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h2474, hlam, p4262_0]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3236, hlam, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3679, hlam, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3846, h4228, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [hlam, p4262_0]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3846, h4228, hc03, hc45, hlam, hphi, ht34, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3846, hlam, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4156, hlam, p4262_0]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h2474, h4259, hc01, hc12, hlam, hphi, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3845, hlam, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [hlam, p4262_0]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4224, hlam, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4226, hlam, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4228, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4228, hc02, hc45, hlam, hphi, ht23, ht34, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4228, hc03, hc45, hlam, hphi, ht34, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [hlam, p4262_0]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4228, hlam, p4262_0]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3679, hc01, hc15, hlam, hphi, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h3845, h4156, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h2474, h4226, hc01, hc35, hlam, hphi, ht12, ht23, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [h4228, hc04, hc45, hlam, hphi, p4262_1]
                · have p4262_0 := h4262c.1
                  have p4262_1 := h4262c.2.1
                  have p4262_2 := h4262c.2.2.1
                  have p4262_3 := h4262c.2.2.2
                  linarith only [hlam, p4262_0]
            · linarith only [h3845, h3846, h4259, hc12, hc24, hlam, hphi]

end R2N4
