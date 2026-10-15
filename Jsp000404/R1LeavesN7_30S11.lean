import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S5
import Jsp000404.R1LeavesN7_30S7
import Jsp000404.R1LeavesN7_30S8
import Jsp000404.R1LeavesN7_30S9
import Jsp000404.R1LeavesN7_30S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3679 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3845 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4289 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h4477 | h4477
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4478 | h4478
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4479 | h4479
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4480 | h4480
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4481 | h4481
          · linarith only [h3845, h4477, h4481, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4483 | h4483
            · rcases h0bigk with h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h0, hlam, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h2474, hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3236, hlam, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3679, hlam, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3845, hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h4289, hlam, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [hc02, hlam, hphi, ht0b, ht5b, p4484_1, u5ehi0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3845, hc02, hc23, hlam, hphi, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3845, h4480, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1, u5ehi4]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3845, h4477, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1, u5ehi2]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h4289, h4477, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1, u5ehi2]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h4478, hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3845, h4477, h4478, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1, u5ehi2]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h4477, hlam, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h4479, hlam, p4484_0]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [h4480, hlam, p4484_1]
              · have p4484_0 := h4484c.1
                have p4484_1 := h4484c.2.1
                have p4484_2 := h4484c.2.2.1
                have p4484_3 := h4484c.2.2.2
                linarith only [hlam, p4484_0]
            · linarith only [h2474, h4478, h4481, h4483, hlam]
        · linarith only [h4289, h4477, h4480, hlam]
      · linarith only [h3845, h4477, h4479, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4513 | h4513
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4514 | h4514
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4515 | h4515
          · linarith only [h3845, h4477, h4515, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4517 | h4517
            · linarith only [h3845, h4477, h4478, h4517, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · linarith only [h3845, h4477, h4517, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h3845, h4477, h4478, h4514, hlam]
      · linarith only [h3845, h4477, h4513, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4522 | h4522
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4523 | h4523
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4524 | h4524
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4525 | h4525
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4526 | h4526
            · rcases h0bigk with h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c | h4527c
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h0, hlam, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h2474, hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3236, hlam, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3679, hlam, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h4289, h4525, h4526, hc01, hc12, hlam, hphi, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3845, hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h4289, hlam, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h4477, hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3845, h4525, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3845, h4524, h4525, hc12, hlam, hphi, ht01, ht0b, ht5b, p4527_1, u5ehi4]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3845, h4525, hc12, hlam, hphi, ht01, ht0b, ht5b, p4527_1, u5ehi0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h0, h4289, h4525, h4526, hc01, hc12, hlam, hphi, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h4522, hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h4289, h4523, h4525, h4526, hc12, hlam, hphi, ht01, ht0b, ht5b, p4527_1, u5ehi3]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h4523, hlam, p4527_0]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [h4524, hlam, p4527_1]
              · have p4527_0 := h4527c.1
                have p4527_1 := h4527c.2.1
                have p4527_2 := h4527c.2.2.1
                have p4527_3 := h4527c.2.2.2
                linarith only [hlam, p4527_0]
            · linarith only [h3845, h4522, h4526, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4554 | h4554
            · rcases h0bigk with h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c | h4555c
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h0, hlam, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h2474, hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3236, hlam, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3679, hlam, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3845, hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h4289, hlam, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h4477, hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3845, hc02, hc23, hlam, hphi, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3845, h4524, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4555_1, u5ehi0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3845, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4555_1, u5ehi0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h0, h4289, hc01, hc24, hlam, hphi, ht12, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h4522, hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3845, h4522, h4523, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4555_1, u5ehi3]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h4523, hlam, p4555_0]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [h4524, hlam, p4555_1]
              · have p4555_0 := h4555c.1
                have p4555_1 := h4555c.2.1
                have p4555_2 := h4555c.2.2.1
                have p4555_3 := h4555c.2.2.2
                linarith only [hlam, p4555_0]
            · linarith only [h2474, h4522, h4525, h4554, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4582 | h4582
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4583 | h4583
            · rcases h0bigk with h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h0, hlam, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h2474, hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3236, hlam, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3679, hlam, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3845, hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h4289, hlam, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h4477, hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3845, hc01, hc23, hlam, hphi, ht12, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3845, hc02, hc23, hlam, hphi, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3236, h3845, hc01, hc23, hlam, hphi, ht12, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3845, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4584_1, u5ehi0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h0, h4289, h4583, hc01, hc23, hlam, hphi, ht12, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h4522, hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h4524, hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h4523, hlam, p4584_0]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [h4524, hc04, hc45, hlam, hphi, p4584_1]
              · have p4584_0 := h4584c.1
                have p4584_1 := h4584c.2.1
                have p4584_2 := h4584c.2.2.1
                have p4584_3 := h4584c.2.2.2
                linarith only [hlam, p4584_0]
            · linarith only [h3845, h4522, h4583, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4611 | h4611
            · rcases h0bigk with h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c | h4612c
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h0, hlam, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h2474, hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h3236, hlam, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h3679, hlam, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h3845, hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h4289, hlam, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h4477, hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h3845, hc02, hc23, hlam, hphi, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h0, h3845, h4289, hc01, hc23, hlam, hphi, ht12, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h3845, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4612_1, u5ehi0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h0, h4289, hc01, hc24, hlam, hphi, ht12, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h4522, hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h4524, hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h4523, hlam, p4612_0]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [h4524, hc04, hc45, hlam, hphi, p4612_1]
              · have p4612_0 := h4612c.1
                have p4612_1 := h4612c.2.1
                have p4612_2 := h4612c.2.2.1
                have p4612_3 := h4612c.2.2.2
                linarith only [hlam, p4612_0]
            · linarith only [h0, h4582, h4611, hc01, hc34, hlam, hphi, ht12, ht23]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4639 | h4639
        · linarith only [h4522, h4523, h4639, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4641 | h4641
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4642 | h4642
            · rcases h0bigk with h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c | h4643c
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h0, hlam, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h2474, hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h3236, hlam, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h3679, hlam, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h3845, hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4289, hlam, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4477, hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4523, hc01, hc35, hlam, hphi, ht12, ht23, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4523, hc02, hc35, hlam, hphi, ht23, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4523, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4523, hlam, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4639, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h0, h4639, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4522, hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4639, hlam, p4643_0]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4523, hc03, hc35, hlam, hphi, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [h4639, hc04, hc45, hlam, hphi, p4643_1]
              · have p4643_0 := h4643c.1
                have p4643_1 := h4643c.2.1
                have p4643_2 := h4643c.2.2.1
                have p4643_3 := h4643c.2.2.2
                linarith only [hlam, p4643_0]
            · linarith only [h0, h2474, h3845, h4522, h4642, hc01, hc13, hlam, hphi]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4670 | h4670
            · rcases h0bigk with h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c | h4671c
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h0, hlam, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h2474, hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h3236, hlam, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h3679, hlam, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4289, hc01, hc24, hlam, hphi, ht12, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h3845, hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4289, hlam, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4477, hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4523, hc01, hc35, hlam, hphi, ht12, ht23, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4523, hc02, hc35, hlam, hphi, ht23, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4523, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4523, hlam, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h0, h4289, hc01, hc24, hlam, hphi, ht12, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4522, hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4639, hlam, p4671_0]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4639, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h0, h4639, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h4639, hc03, hc45, hlam, hphi, ht34, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [h0, h4289, h4639, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4671_1]
              · have p4671_0 := h4671c.1
                have p4671_1 := h4671c.2.1
                have p4671_2 := h4671c.2.2.1
                have p4671_3 := h4671c.2.2.2
                linarith only [hlam, p4671_0]
            · linarith only [h0, h4522, h4641, h4670, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4698 | h4698
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4699 | h4699
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4700 | h4700
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4701 | h4701
            · linarith only [h4522, h4698, h4700, h4701, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases h0bigk with h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c | h4703c
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h0, hlam, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h2474, hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h3236, hlam, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h3679, hlam, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h3845, hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h4289, hlam, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h4477, hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h2474, h4700, hc01, hc12, hlam, hphi, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h3845, h4701, hc02, hc34, hlam, hphi, ht23, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h4522, hlam, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h3845, h4701, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4703_1, u5ehi0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h0, h4289, h4701, hc01, hc34, hlam, hphi, ht12, ht23, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h4289, h4701, hc03, hc34, hlam, hphi, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h4289, h4698, h4701, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4703_1, u5ehi3]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h4698, hlam, p4703_0]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [h4699, hlam, p4703_1]
              · have p4703_0 := h4703c.1
                have p4703_1 := h4703c.2.1
                have p4703_2 := h4703c.2.2.1
                have p4703_3 := h4703c.2.2.2
                linarith only [hlam, p4703_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4729 | h4729
            · linarith only [h4522, h4698, h4729, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h0, h4700, h4729, hc01, hc34, hlam, hphi, ht12, ht23]
        · linarith only [h4522, h4698, h4699, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4733 | h4733
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4734 | h4734
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4735 | h4735
            · linarith only [h2474, h4522, h4734, h4735, hc01, hc12, hlam, hphi]
            · rcases h0bigk with h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c | h4737c
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [hlam, p4737_0]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h0, hlam, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h2474, hlam, p4737_0]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h3236, hlam, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h3679, hlam, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h3845, h4698, hc01, hc35, hlam, hphi, ht12, ht23, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [hlam, p4737_0]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h3845, hlam, p4737_0]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4289, hlam, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4477, hlam, p4737_0]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4698, hc01, hc35, hlam, hphi, ht12, ht23, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4698, hc02, hc35, hlam, hphi, ht23, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [hlam, p4737_0]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4522, hlam, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4698, hlam, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h0, h4289, hc01, hc24, hlam, hphi, ht12, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4522, hc03, hc34, hlam, hphi, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [hlam, p4737_0]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h0, h3845, h4522, h4698, hc01, hc34, hlam, hphi, ht12, ht23, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h0, h3845, h4698, hc01, hc35, hlam, hphi, ht12, ht23, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [h4733, hlam, p4737_1]
              · have p4737_0 := h4737c.1
                have p4737_1 := h4737c.2.1
                have p4737_2 := h4737c.2.2.1
                have p4737_3 := h4737c.2.2.2
                linarith only [hlam, p4737_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4763 | h4763
            · rcases h0bigk with h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [hlam, p4764_0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h0, hlam, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h2474, hlam, p4764_0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h3236, hlam, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h3679, hlam, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h0, h4734, hc01, hc23, hlam, hphi, ht12, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [hlam, p4764_0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h3845, hlam, p4764_0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4289, hlam, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4477, hlam, p4764_0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h3845, hc02, hc23, hlam, hphi, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [hlam, p4764_0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4522, hlam, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4698, hlam, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4522, h4763, hc01, hc23, hlam, hphi, ht12, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h0, h4522, h4763, hc01, hc23, hlam, hphi, ht12, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4522, h4763, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [hlam, p4764_0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4522, h4763, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4764_1, u5ehi0]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h3679, hc01, hc15, hlam, hphi, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h0, h4477, hc01, hc25, hlam, hphi, ht12, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h0, h3845, h4698, hc01, hc35, hlam, hphi, ht12, ht23, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [h4733, hlam, p4764_1]
              · have p4764_0 := h4764c.1
                have p4764_1 := h4764c.2.1
                have p4764_2 := h4764c.2.2.1
                have p4764_3 := h4764c.2.2.2
                linarith only [hlam, p4764_0]
            · linarith only [h0, h4734, h4763, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4791 | h4791
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4792 | h4792
            · linarith only [h0, h3845, h4522, h4791, h4792, hc01, hc12, hlam, hphi]
            · rcases h0bigk with h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h0, hlam, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h2474, hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h3236, hlam, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h3679, hlam, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h3845, hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4289, hlam, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4477, hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h2474, hc01, hc13, hlam, hphi, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h0, h2474, hc01, hc13, hlam, hphi, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4522, hlam, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4698, hlam, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h0, h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4733, hc03, hc45, hlam, hphi, ht34, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4733, hlam, p4794_0]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h0, h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h0, h3845, h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [h4733, hc04, hc45, hlam, hphi, p4794_1]
              · have p4794_0 := h4794c.1
                have p4794_1 := h4794c.2.1
                have p4794_2 := h4794c.2.2.1
                have p4794_3 := h4794c.2.2.2
                linarith only [hlam, p4794_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4820 | h4820
            · rcases h0bigk with h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h0, hlam, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h2474, hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h3236, hlam, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h3679, hlam, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h3845, hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4289, hlam, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4477, hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h2474, h4791, hc01, hc23, hlam, hphi, ht12, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h2474, h4791, hc02, hc23, hlam, hphi, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4522, hlam, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4698, hlam, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h3236, hc01, hc14, hlam, hphi, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h0, h4289, hc01, hc24, hlam, hphi, ht12, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4522, h4820, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4733, hlam, p4821_0]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h0, h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h0, h3845, h4733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [h4733, hc04, hc45, hlam, hphi, p4821_1]
              · have p4821_0 := h4821c.1
                have p4821_1 := h4821c.2.1
                have p4821_2 := h4821c.2.2.1
                have p4821_3 := h4821c.2.2.2
                linarith only [hlam, p4821_0]
            · linarith only [h0, h4791, h4820, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3679 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3845 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h4289 | h4289
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h2474 h3236 h3679 h3845 h4289
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h2474 h3236 h3679 h3845 h4289

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3679 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h3845 | h3845
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h2474 h3236 h3679 h3845
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h2474 h3236 h3679 h3845

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h3679 | h3679
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h2474 h3236 h3679
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h2474 h3236 h3679

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h3236 | h3236
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h2474 h3236
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h2474 h3236

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h2474 | h2474
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x0 m hb0 hb2 hb3 hb5 h0 h2474
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1 m hb0 hb2 hb3 hb5 h0 h2474

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
