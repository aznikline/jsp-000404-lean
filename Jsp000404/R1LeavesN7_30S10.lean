import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3679 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3845 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4289 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h4290 | h4290
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4291 | h4291
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4292 | h4292
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4293 | h4293
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4294 | h4294
          · linarith only [h3845, h4290, h4294, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4296 | h4296
            · rcases h0bigk with h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c | h4297c
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h0, hlam, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h2474, hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h3236, hlam, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h3679, hlam, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h0, h4294, hc01, hc23, hlam, hphi, ht12, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h3845, hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h4293, hc02, hlam, hphi, ht0b, ht5b, p4297_1, u5ehi0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h0, h4294, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4297_1, u5ehi0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h2474, h4294, hc01, hc23, hlam, hphi, ht12, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h2474, h4294, hc02, hc23, hlam, hphi, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h2474, h3236, h4294, hc01, hc23, hlam, hphi, ht12, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h2474, h4290, h4294, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4297_1, u5ehi2]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h4289, hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h4291, hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h0, h4289, h4290, h4294, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4297_1, u5ehi2]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h4290, hlam, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h4292, hlam, p4297_0]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [h4293, hlam, p4297_1]
              · have p4297_0 := h4297c.1
                have p4297_1 := h4297c.2.1
                have p4297_2 := h4297c.2.2.1
                have p4297_3 := h4297c.2.2.2
                linarith only [hlam, p4297_0]
            · linarith only [h0, h4294, h4296, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4324 | h4324
          · linarith only [h3845, h4290, h4324, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4326 | h4326
            · rcases h0bigk with h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c | h4327c
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h0, hlam, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h2474, hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h3236, hlam, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h3679, hlam, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h3845, hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h0, h4324, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h0, h4324, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4327_1, u5ehi0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h3845, hc02, hc23, hlam, hphi, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h3236, h3845, hc01, hc23, hlam, hphi, ht12, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h3845, h4292, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4327_1, u5ehi3]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h4293, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h4289, hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h4291, hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h4293, hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h4290, hlam, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h4292, hlam, p4327_0]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [h0, h4290, h4324, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4327_1]
              · have p4327_0 := h4327c.1
                have p4327_1 := h4327c.2.1
                have p4327_2 := h4327c.2.2.1
                have p4327_3 := h4327c.2.2.2
                linarith only [hlam, p4327_0]
            · linarith only [h0, h4324, h4326, hc01, hc34, hlam, hphi, ht12, ht23]
      · linarith only [h3845, h4290, h4292, hlam]
    · linarith only [h3845, h4289, h4291, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4356 | h4356
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4357 | h4357
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4358 | h4358
        · linarith only [h4289, h4290, h4358, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4360 | h4360
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4361 | h4361
            · rcases h0bigk with h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c | h4362c
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h0, hlam, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h2474, hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3236, hlam, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3679, hlam, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3845, h4360, hc01, hc12, hlam, hphi, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3845, hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3845, h4360, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h4290, hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3845, h4360, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3236, h3845, h4360, hc01, hc12, hlam, hphi, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3845, h4289, h4290, h4360, h4361, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h4358, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h4289, hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h4356, hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h4358, hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h4289, h4290, h4361, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h4357, hlam, p4362_0]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [h3845, h4357, h4360, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4362_1]
              · have p4362_0 := h4362c.1
                have p4362_1 := h4362c.2.1
                have p4362_2 := h4362c.2.2.1
                have p4362_3 := h4362c.2.2.2
                linarith only [hlam, p4362_0]
            · linarith only [h3845, h4356, h4361, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4389 | h4389
            · rcases h0bigk with h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h0, hlam, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h2474, hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3236, hlam, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3679, hlam, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3845, hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h0, h3236, h4360, hc01, hc23, hlam, hphi, ht12, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h4290, hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3845, hc01, hc23, hlam, hphi, ht12, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3845, hc02, hc23, hlam, hphi, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3236, h3845, hc01, hc23, hlam, hphi, ht12, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3845, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4390_1, u5ehi0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h4289, hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h4356, hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h4358, hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h4290, hc02, hc25, hlam, hphi, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h4357, hlam, p4390_0]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [h4358, hc04, hc45, hlam, hphi, p4390_1]
              · have p4390_0 := h4390c.1
                have p4390_1 := h4390c.2.1
                have p4390_2 := h4390c.2.2.1
                have p4390_3 := h4390c.2.2.2
                linarith only [hlam, p4390_0]
            · linarith only [h0, h4360, h4389, hc01, hc34, hlam, hphi, ht12, ht23]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4417 | h4417
        · linarith only [h4289, h4290, h4417, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4419 | h4419
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4420 | h4420
            · rcases h0bigk with h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h0, hlam, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h2474, hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h3236, hlam, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h3679, hlam, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h3845, h4419, hc01, hc13, hlam, hphi, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h3845, hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h3845, h4419, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4290, hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4357, hc01, hc35, hlam, hphi, ht12, ht23, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4357, hc02, hc35, hlam, hphi, ht23, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h3236, h4357, hc01, hc35, hlam, hphi, ht12, ht23, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4357, hlam, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4289, hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4356, hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4417, hlam, p4421_0]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4289, h4417, h4420, hc34, hc45, hlam, hphi, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4417, hc03, hc45, hlam, hphi, ht34, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [h4417, hc04, hc45, hlam, hphi, p4421_1]
              · have p4421_0 := h4421c.1
                have p4421_1 := h4421c.2.1
                have p4421_2 := h4421c.2.2.1
                have p4421_3 := h4421c.2.2.2
                linarith only [hlam, p4421_0]
            · linarith only [h3845, h4289, h4356, h4420, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4448 | h4448
            · rcases h0bigk with h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h0, hlam, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h2474, hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h3236, hlam, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h3679, hlam, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h0, h4419, hc01, hc23, hlam, hphi, ht12, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h3845, hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h3236, h3845, h4357, hc01, hc35, hlam, hphi, ht12, ht23, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4290, hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4357, hc01, hc35, hlam, hphi, ht12, ht23, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4357, hc02, hc35, hlam, hphi, ht23, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h3236, h4357, hc01, hc35, hlam, hphi, ht12, ht23, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4357, hlam, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4289, hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4356, hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4417, hlam, p4449_0]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4417, hc02, hc45, hlam, hphi, ht23, ht34, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h4417, hc03, hc45, hlam, hphi, ht34, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [h3236, h4417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4449_1]
              · have p4449_0 := h4449c.1
                have p4449_1 := h4449c.2.1
                have p4449_2 := h4449c.2.2.1
                have p4449_3 := h4449c.2.2.2
                linarith only [hlam, p4449_0]
            · linarith only [h0, h4419, h4448, hc01, hc34, hlam, hphi, ht12, ht23]
    · linarith only [h3845, h4289, h4356, hlam]

end R2N4
