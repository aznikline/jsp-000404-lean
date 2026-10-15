import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_31S10
import Jsp000404.R1LeavesN7_31S11
import Jsp000404.R1LeavesN7_31S12
import Jsp000404.R1LeavesN7_31S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3271 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3539 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3826 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h4379 | h4379
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4380 | h4380
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4381 | h4381
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4382 | h4382
        · linarith only [h0, h3826, h4382, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4384 | h4384
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4385 | h4385
            · linarith only [h4381, h4382, h4385, hlam]
            · linarith only [h2837, h4379, h4385, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4388 | h4388
            · linarith only [h4381, h4382, h4388, hlam]
            · linarith only [h2837, h4379, h4388, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4391 | h4391
        · linarith only [h0, h3826, h4381, h4391, hc01, hlam, hphi, u1elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4393 | h4393
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4394 | h4394
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4395 | h4395
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4396 | h4396
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4397 | h4397
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4398 | h4398
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4399 | h4399
                      · rcases h1bigk with h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c | h4400c
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h0, hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h2837, hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h3271, hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h3539, hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4391, h4394, hc01, hlam, hphi, p4400_1, u1elo2]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4381, hlam, p4400_1]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4391, hlam, p4400_1]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h3539, h4391, h4394, hc01, hlam, hphi, p4400_1, u1elo2]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [hc01, hlam, hphi, p4400_1, u1elo2]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4393, hc25, hlam, hphi, ht01, ht0b, ht5b, p4400_1, u1elo2]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4400_1, u1elo2]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4400_1, u1elo2]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [hc01, hlam, hphi, p4400_1, u1elo3]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h3539, h4393, hc01, hlam, hphi, p4400_1, u1elo3]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4394, hlam, p4400_1]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h3539, h4394, hc01, hlam, hphi, p4400_1, u1elo2]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4393, hc01, hlam, hphi, p4400_1, u1elo1]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4393, hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4395, hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [h4396, hlam, p4400_0]
                        · have p4400_0 := h4400c.1
                          have p4400_1 := h4400c.2.1
                          have p4400_2 := h4400c.2.2.1
                          have p4400_3 := h4400c.2.2.2
                          linarith only [hlam, p4400_0]
                      · rcases h1bigk with h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h0, hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h2837, hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h3271, hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h3539, hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4391, h4397, hc01, hc23, hlam, hphi, ht12, p4426_1]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4381, hlam, p4426_1]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4391, hlam, p4426_1]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h3539, h4391, h4397, hc01, hc23, hlam, hphi, ht12, p4426_1]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hc01, hlam, hphi, p4426_1, u1elo2]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4393, hc25, hlam, hphi, ht01, ht0b, ht5b, p4426_1, u1elo2]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4426_1, u1elo2]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4426_1, u1elo2]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hc01, hlam, hphi, p4426_1, u1elo3]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4393, h4398, h4399, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4426_1, u1elo3]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4394, hlam, p4426_1]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h3539, h4394, hc01, hlam, hphi, p4426_1, u1elo2]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hc01, hlam, hphi, p4426_1, u1elo4]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4393, hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4395, hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [h4396, hlam, p4426_0]
                        · have p4426_0 := h4426c.1
                          have p4426_1 := h4426c.2.1
                          have p4426_2 := h4426c.2.2.1
                          have p4426_3 := h4426c.2.2.2
                          linarith only [hlam, p4426_0]
                    · linarith only [h0, h2837, h3826, h4379, h4380, h4398, hc01, hlam, hphi, u1elo2]
                  · linarith only [h3539, h4381, h4393, h4397, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3271, h4380, h4396, hlam]
              · linarith only [h4381, h4393, h4395, hlam]
            · linarith only [h2837, h4379, h4394, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4457 | h4457
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4458 | h4458
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4459 | h4459
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4460 | h4460
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4461 | h4461
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4462 | h4462
                      · rcases h1bigk with h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c | h4463c
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h0, hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h2837, hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h3271, hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h3539, hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hc01, hlam, hphi, p4463_1, u1elo1]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h4381, hlam, p4463_1]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h4391, hlam, p4463_1]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h4393, hlam, p4463_1]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hc01, hlam, hphi, p4463_1, u1elo2]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4463_1, u1elo2]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h0, h4393, h4459, hc01, hlam, hphi, p4463_1, u1elo2]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h0, h4393, hc01, hlam, hphi, p4463_1, u1elo2]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hc01, hlam, hphi, p4463_1, u1elo3]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4463_1, u1elo3]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h4457, hlam, p4463_1]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h0, h4393, h4457, hc01, hlam, hphi, p4463_1, u1elo2]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hc01, hlam, hphi, p4463_1, u1elo4]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4463_1, u1elo4]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h4458, hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [h4459, hlam, p4463_0]
                        · have p4463_0 := h4463c.1
                          have p4463_1 := h4463c.2.1
                          have p4463_2 := h4463c.2.2.1
                          have p4463_3 := h4463c.2.2.2
                          linarith only [hlam, p4463_0]
                      · rcases h1bigk with h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c | h4489c
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h0, hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h2837, hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h3271, hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h3539, hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hc01, hlam, hphi, p4489_1, u1elo1]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h4381, hlam, p4489_1]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h4391, hlam, p4489_1]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h4393, hlam, p4489_1]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hc01, hlam, hphi, p4489_1, u1elo2]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4489_1, u1elo2]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4489_1, u1elo2]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h0, h4393, hc01, hlam, hphi, p4489_1, u1elo2]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hc01, hlam, hphi, p4489_1, u1elo3]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4489_1, u1elo3]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h4457, hlam, p4489_1]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h0, h4393, h4457, hc01, hlam, hphi, p4489_1, u1elo2]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hc01, hlam, hphi, p4489_1, u1elo4]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4489_1, u1elo4]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h4458, hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [h4459, hlam, p4489_0]
                        · have p4489_0 := h4489c.1
                          have p4489_1 := h4489c.2.1
                          have p4489_2 := h4489c.2.2.1
                          have p4489_3 := h4489c.2.2.2
                          linarith only [hlam, p4489_0]
                    · linarith only [h0, h2837, h3826, h4379, h4380, h4461, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h4381, h4460, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2837, h3271, h4379, h4380, h4459, hc01, hlam, hphi, u1elo2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4518 | h4518
                · linarith only [h4457, h4458, h4518, hlam]
                · linarith only [h2837, h3271, h4379, h4380, h4458, h4518, hc01, hc35, hlam, hphi, ht12, ht23]
            · linarith only [h2837, h4379, h4457, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4522 | h4522
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4523 | h4523
        · linarith only [h0, h3826, h4523, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4525 | h4525
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4526 | h4526
            · linarith only [h4522, h4523, h4526, hlam]
            · linarith only [h2837, h4379, h4526, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4529 | h4529
            · linarith only [h4522, h4523, h4529, hlam]
            · linarith only [h2837, h4379, h4529, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4532 | h4532
        · linarith only [h0, h3826, h4522, h4532, hc01, hlam, hphi, u1elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4534 | h4534
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4535 | h4535
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4536 | h4536
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4537 | h4537
                · linarith only [h0, h3826, h4380, h4535, h4537, hc01, hlam, hphi, u1elo2]
                · linarith only [h4532, h4534, h4537, hlam]
              · linarith only [h4532, h4534, h4535, h4536, hlam]
            · linarith only [h2837, h4379, h4535, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4542 | h4542
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4543 | h4543
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4544 | h4544
                · linarith only [h0, h3826, h4380, h4544, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4546 | h4546
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4547 | h4547
                    · linarith only [h0, h4532, h4544, h4546, h4547, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h4532, h4547, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h4522, h4546, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4551 | h4551
                · linarith only [h3271, h4380, h4551, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4553 | h4553
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4554 | h4554
                    · linarith only [h3271, h4551, h4553, h4554, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h4532, h4554, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h2837, h4379, h4543, h4553, hc23, hc35, hlam, hphi]
            · linarith only [h2837, h4379, h4542, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4559 | h4559
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4560 | h4560
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4561 | h4561
        · linarith only [h0, h3826, h4561, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4563 | h4563
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4564 | h4564
            · linarith only [h2837, h4379, h4564, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4566 | h4566
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4567 | h4567
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4568 | h4568
                  · linarith only [h4560, h4561, h4564, h4568, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4570 | h4570
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4571 | h4571
                      · rcases h1bigk with h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c | h4572c
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h0, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h2837, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h3271, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h3539, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4561, h4568, hc01, hc34, hlam, hphi, ht12, ht23, p4572_1]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h3539, h4561, h4566, h4568, hc01, hc34, hlam, hphi, ht12, ht23, p4572_1]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4561, hlam, p4572_1]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h3539, h4561, h4568, hc01, hc34, hlam, hphi, ht12, ht23, p4572_1]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [hc01, hlam, hphi, p4572_1, u1elo2]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4560, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4564, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h3539, h4560, h4561, h4568, hc01, hc34, hlam, hphi, ht12, ht23, p4572_1]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [hc01, hlam, hphi, p4572_1, u1elo3]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4560, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4572_1, u1elo3]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4572_1, u1elo3]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4572_1, u1elo3]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4560, h4566, hc01, hlam, hphi, p4572_1, u1elo1]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4563, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4566, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [h4567, hlam, p4572_0]
                        · have p4572_0 := h4572c.1
                          have p4572_1 := h4572c.2.1
                          have p4572_2 := h4572c.2.2.1
                          have p4572_3 := h4572c.2.2.2
                          linarith only [hlam, p4572_0]
                      · linarith only [h4559, h4561, h4563, h4568, h4571, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h3271, h3539, h4559, h4560, h4561, h4566, h4570, hc01, hlam, hphi, u1elo3]
                · linarith only [h3271, h4559, h4567, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4601 | h4601
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4602 | h4602
                  · linarith only [h4379, h4559, h4560, h4561, h4602, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4604 | h4604
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4605 | h4605
                      · rcases h1bigk with h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c | h4606c
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h0, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h2837, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h3271, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h3539, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4561, h4602, hc01, hc34, hlam, hphi, ht12, ht23, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h2837, h4561, h4602, hc01, hc34, hlam, hphi, ht12, ht23, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4561, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h2837, h4561, h4566, h4602, hc01, hc34, hlam, hphi, ht12, ht23, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hc01, hlam, hphi, p4606_1, u1elo2]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4560, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4564, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4566, hlam, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hc01, hlam, hphi, p4606_1, u1elo3]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4560, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4606_1, u1elo3]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4606_1, u1elo3]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h2837, h4566, hc01, hlam, hphi, p4606_1, u1elo3]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4563, hc01, hlam, hphi, p4606_1, u1elo1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4563, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h2837, h4561, h4563, h4602, hc01, hc34, hlam, hphi, ht12, ht23, p4606_1]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [h4601, hlam, p4606_0]
                        · have p4606_0 := h4606c.1
                          have p4606_1 := h4606c.2.1
                          have p4606_2 := h4606c.2.2.1
                          have p4606_3 := h4606c.2.2.2
                          linarith only [hlam, p4606_0]
                      · linarith only [h4559, h4561, h4563, h4602, h4605, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2837, h3271, h4559, h4561, h4563, h4566, h4604, hc01, hlam, hphi, u1elo3]
                · linarith only [h3271, h4559, h4601, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4635 | h4635
            · linarith only [h2837, h4379, h4635, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4637 | h4637
              · linarith only [h4560, h4563, h4637, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4639 | h4639
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4640 | h4640
                  · linarith only [h2837, h4635, h4640, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4642 | h4642
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4643 | h4643
                      · rcases h1bigk with h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h0, hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h2837, hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h3271, hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h3539, hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hc01, hlam, hphi, p4644_1, u1elo1]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h2837, h4563, h4640, h4642, hc01, hc34, hlam, hphi, ht12, ht23, p4644_1]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h4561, hlam, p4644_1]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h4563, hlam, p4644_1]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hc01, hlam, hphi, p4644_1, u1elo2]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h4560, hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h4635, hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h4637, hlam, p4644_1]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hc01, hlam, hphi, p4644_1, u1elo3]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h4560, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4644_1, u1elo3]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4644_1, u1elo3]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4644_1, u1elo3]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hc01, hlam, hphi, p4644_1, u1elo4]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h2837, h4560, hc01, hlam, hphi, p4644_1, u1elo4]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4644_1, u1elo4]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [h4639, hlam, p4644_0]
                        · have p4644_0 := h4644c.1
                          have p4644_1 := h4644c.2.1
                          have p4644_2 := h4644c.2.2.1
                          have p4644_3 := h4644c.2.2.2
                          linarith only [hlam, p4644_0]
                      · linarith only [h0, h3271, h3826, h4559, h4640, h4643, hc01, hlam, hphi, u1elo3]
                    · linarith only [h2837, h3271, h4559, h4560, h4561, h4642, hc01, hlam, hphi, u1elo3]
                · linarith only [h3271, h4559, h4639, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4673 | h4673
        · linarith only [h0, h3826, h4673, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4675 | h4675
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4676 | h4676
            · linarith only [h2837, h4379, h4676, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4678 | h4678
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4679 | h4679
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4680 | h4680
                  · linarith only [h0, h4560, h4676, h4680, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h3539, h4560, h4675, h4680, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3271, h4559, h4679, hlam]
              · linarith only [h4560, h4675, h4678, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4685 | h4685
            · linarith only [h2837, h4379, h4685, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4687 | h4687
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4688 | h4688
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4689 | h4689
                  · linarith only [h2837, h4685, h4689, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h4560, h4689, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3271, h4559, h4688, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4693 | h4693
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4694 | h4694
                  · linarith only [h0, h4560, h4685, h4694, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h4560, h4694, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3271, h4559, h4693, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4698 | h4698
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4699 | h4699
        · linarith only [h0, h3826, h4699, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4701 | h4701
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4702 | h4702
            · linarith only [h2837, h4379, h4702, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4704 | h4704
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4705 | h4705
                · linarith only [h3271, h4559, h4705, hc01, hlam, hphi, u1elo3]
                · linarith only [h4698, h4699, h4704, h4705, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4708 | h4708
                · linarith only [h0, h3826, h4559, h4708, hc01, hlam, hphi, u1elo3]
                · linarith only [h4699, h4701, h4708, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4711 | h4711
            · linarith only [h2837, h4379, h4711, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4713 | h4713
              · linarith only [h4698, h4701, h4713, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4715 | h4715
                · linarith only [h0, h3826, h4559, h4715, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4717 | h4717
                  · linarith only [h4698, h4699, h4711, h4715, h4717, hc13, hc45, hlam, hphi, ht34]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4719 | h4719
                    · linarith only [h4698, h4699, h4715, h4717, h4719, hc23, hc34, hlam, hphi]
                    · linarith only [h2837, h4698, h4699, h4719, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4722 | h4722
        · linarith only [h0, h3826, h4722, hc01, hlam, hphi, u1elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4724 | h4724
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4725 | h4725
            · linarith only [h2837, h4379, h4725, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4727 | h4727
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4728 | h4728
                · linarith only [h0, h3826, h4559, h4728, hc01, hlam, hphi, u1elo3]
                · linarith only [h4698, h4724, h4725, h4728, hlam]
              · linarith only [h4698, h4724, h4727, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4732 | h4732
            · linarith only [h2837, h4379, h4732, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4734 | h4734
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4735 | h4735
                · linarith only [h0, h3826, h4559, h4735, hc01, hlam, hphi, u1elo3]
                · linarith only [h4732, h4734, h4735, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4738 | h4738
                · linarith only [h0, h3826, h4559, h4738, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4740 | h4740
                  · linarith only [h0, h4698, h4732, h4740, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h4698, h4740, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3271 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3539 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3826 | h3826
  · exact r1l7_21_14_M_LI_L_I_x1_x1_x1_x1_x0 m hb1 hb4 h0 h2837 h3271 h3539 h3826
  · exact r1l7_21_14_M_LI_L_I_x1_x1_x1_x1_x1 m hb1 hb4 h0 h2837 h3271 h3539 h3826

set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3271 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3539 | h3539
  · exact r1l7_21_14_M_LI_L_I_x1_x1_x1_x0 m hb1 hb4 h0 h2837 h3271 h3539
  · exact r1l7_21_14_M_LI_L_I_x1_x1_x1_x1 m hb1 hb4 h0 h2837 h3271 h3539

set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h3271 | h3271
  · exact r1l7_21_14_M_LI_L_I_x1_x1_x0 m hb1 hb4 h0 h2837 h3271
  · exact r1l7_21_14_M_LI_L_I_x1_x1_x1 m hb1 hb4 h0 h2837 h3271

set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2837 | h2837
  · exact r1l7_21_14_M_LI_L_I_x1_x0 m hb1 hb4 h0 h2837
  · exact r1l7_21_14_M_LI_L_I_x1_x1 m hb1 hb4 h0 h2837

set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_14_M_LI_L_I_x0 m hb1 hb4 h0
  · exact r1l7_21_14_M_LI_L_I_x1 m hb1 hb4 h0

end R2N4
