import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2475 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h2476 | h2476
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2477 | h2477
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2478 | h2478
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2479 | h2479
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2480 | h2480
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2481 | h2481
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2482 | h2482
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2483 | h2483
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2484 | h2484
                  · rcases h0bigk with h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h0, hlam, p2485_1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2480, h2482, hc01, hlam, hphi, ht0b, ht5b, p2485_1, u5ehi4]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h0, h2482, hc12, hlam, hphi, ht01, ht0b, ht5b, p2485_1, u5ehi4]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2485_1, u5ehi0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2485_1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h0, h2480, h2482, hc12, hlam, hphi, ht01, ht0b, ht5b, p2485_1, u5ehi4]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h0, h2482, hc12, hlam, hphi, ht01, ht0b, ht5b, p2485_1, u5ehi4]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h0, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2485_1, u5ehi1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2474, hlam, p2485_1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2477, hlam, p2485_1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2482, hc03, hlam, hphi, ht0b, ht5b, p2485_1, u5ehi4]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2474, h2476, hc01, hlam, hphi, ht0b, ht5b, p2485_1, u5ehi1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2475, hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2478, hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2480, hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2476, hc04, hlam, hphi, ht0b, ht5b, p2485_1, u5ehi1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2476, hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2479, hlam, p2485_1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2481, hlam, p2485_0]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [h2482, hlam, p2485_1]
                    · have p2485_0 := h2485c.1
                      have p2485_1 := h2485c.2.1
                      have p2485_2 := h2485c.2.2.1
                      have p2485_3 := h2485c.2.2.2
                      linarith only [hlam, p2485_0]
                  · rcases h0bigk with h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2511_1, u5ehi1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2480, h2484, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2480, h2484, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2511_1, u5ehi1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2474, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2477, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2474, h2480, h2484, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h0, h2474, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2511_1, u5ehi1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2475, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2478, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2480, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2476, hc04, hlam, hphi, ht0b, ht5b, p2511_1, u5ehi1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2476, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2479, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2481, hlam, p2511_0]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [h2482, hlam, p2511_1]
                    · have p2511_0 := h2511c.1
                      have p2511_1 := h2511c.2.1
                      have p2511_2 := h2511c.2.2.1
                      have p2511_3 := h2511c.2.2.2
                      linarith only [hlam, p2511_0]
                · linarith only [h0, h2476, h2483, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2538 | h2538
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2539 | h2539
                  · rcases h0bigk with h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c | h2540c
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, hlam, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2481, hc01, hlam, hphi, ht0b, ht5b, p2540_1, u5ehi3]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2540_1, u5ehi0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, h2481, hc12, hlam, hphi, ht01, ht0b, ht5b, p2540_1, u5ehi3]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      rcases p2540_3 (m.d 0 1) (by simp) with h2549 | h2549
                      · linarith only [h0, h2549, hlam]
                      · linarith only [h2475, h2549, hlam]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, h2479, hc12, hlam, hphi, ht01, ht0b, ht5b, p2540_1, u5ehi2]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2474, hlam, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2477, hlam, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, h2474, h2478, h2539, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, h2474, h2479, hc12, hlam, hphi, ht01, ht0b, ht5b, p2540_1, u5ehi2]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2475, hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2478, hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2480, hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2482, hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2476, hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2479, hlam, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h2481, hlam, p2540_0]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [h0, h2476, h2478, h2539, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2540_1]
                    · have p2540_0 := h2540c.1
                      have p2540_1 := h2540c.2.1
                      have p2540_2 := h2540c.2.2.1
                      have p2540_3 := h2540c.2.2.2
                      linarith only [hlam, p2540_0]
                  · rcases h0bigk with h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, hlam, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, h2480, h2539, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2568_1, u5ehi0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, h2476, h2481, hc12, hlam, hphi, ht01, ht0b, ht5b, p2568_1, u5ehi1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, h2480, h2539, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2568_1, u5ehi1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2474, hlam, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2477, hlam, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2474, h2480, h2539, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h0, h2474, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2568_1, u5ehi1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2475, hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2478, hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2480, hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2482, hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2476, hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2479, hlam, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2481, hlam, p2568_0]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [h2480, h2539, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2568_1]
                    · have p2568_0 := h2568c.1
                      have p2568_1 := h2568c.2.1
                      have p2568_2 := h2568c.2.2.1
                      have p2568_3 := h2568c.2.2.2
                      linarith only [hlam, p2568_0]
                · linarith only [h0, h2476, h2538, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2595 | h2595
              · linarith only [h2480, h2481, h2595, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2597 | h2597
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2598 | h2598
                  · rcases h0bigk with h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, hlam, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2599_1, u5ehi0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, h2474, h2597, h2598, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      rcases p2599_3 (m.d 0 1) (by simp) with h2608 | h2608
                      · linarith only [h0, h2608, hlam]
                      · linarith only [h2475, h2608, hlam]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, h2474, h2481, h2597, h2598, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2474, hlam, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2477, hlam, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2478, h2481, h2598, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2481, hlam, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2475, hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2478, hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2480, hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2595, hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2476, hlam, p2599_0]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2479, hlam, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h2595, hc03, hc45, hlam, hphi, ht34, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [h0, h2476, h2478, h2598, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2599_1]
                    · have p2599_0 := h2599c.1
                      have p2599_1 := h2599c.2.1
                      have p2599_2 := h2599c.2.2.1
                      have p2599_3 := h2599c.2.2.2
                      linarith only [hlam, p2599_0]
                  · linarith only [h2480, h2481, h2598, hc23, hc35, hlam, hphi]
                · linarith only [h0, h2476, h2597, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2629 | h2629
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2630 | h2630
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2631 | h2631
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2632 | h2632
                  · linarith only [h2474, h2480, h2629, h2631, h2632, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases h0bigk with h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, hlam, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, h2629, hc12, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u5ehi3]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, h2480, h2629, hc12, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u5ehi3]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u5ehi0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, h2629, hc12, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u5ehi3]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, h2480, h2629, hc12, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u5ehi3]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u5ehi1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2474, hlam, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2477, hlam, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2480, hlam, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2475, h2476, h2480, hc01, hlam, hphi, ht0b, ht5b, p2634_1, u5ehi1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2475, hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2478, hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, h2475, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h0, h2475, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2634_1, u5ehi1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2476, hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2479, hlam, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2629, hlam, p2634_0]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [h2630, hlam, p2634_1]
                    · have p2634_0 := h2634c.1
                      have p2634_1 := h2634c.2.1
                      have p2634_2 := h2634c.2.2.1
                      have p2634_3 := h2634c.2.2.2
                      linarith only [hlam, p2634_0]
                · linarith only [h0, h2474, h2629, h2631, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h2480, h2629, h2630, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2662 | h2662
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2663 | h2663
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2664 | h2664
                  · linarith only [h0, h2474, h2480, h2663, h2664, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [hlam, p2666_0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, hlam, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, h2474, h2663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2666_1, u5ehi0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [hlam, p2666_0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      rcases p2666_3 (m.d 0 1) (by simp) with h2674 | h2674
                      · linarith only [h0, h2674, hlam]
                      · linarith only [h2474, h2674, hlam]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, h2662, hc12, hlam, hphi, ht01, ht0b, ht5b, p2666_1, u5ehi4]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2666_1, u5ehi1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2474, hlam, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2477, hlam, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [hlam, p2666_0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2480, hlam, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2629, hlam, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2475, hlam, p2666_0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2478, hlam, p2666_0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2474, h2480, h2663, hc23, hc34, hlam, hphi, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [hlam, p2666_0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, h2475, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2666_1, u5ehi1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2476, hlam, p2666_0]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2479, hlam, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h0, h2474, h2476, h2663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [h2662, hlam, p2666_1]
                    · have p2666_0 := h2666c.1
                      have p2666_1 := h2666c.2.1
                      have p2666_2 := h2666c.2.2.1
                      have p2666_3 := h2666c.2.2.2
                      linarith only [hlam, p2666_0]
                · linarith only [h0, h2476, h2663, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2695 | h2695
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2696 | h2696
                  · linarith only [h0, h2474, h2480, h2695, h2696, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c | h2698c
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, hlam, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, h2474, h2695, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2698_1, u5ehi0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      rcases p2698_3 (m.d 0 1) (by simp) with h2706 | h2706
                      · linarith only [h0, h2706, hlam]
                      · linarith only [h2474, h2706, hlam]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      rcases p2698_3 (m.d 0 1) (by simp) with h2709 | h2709
                      · linarith only [h0, h2709, hlam]
                      · linarith only [h2475, h2709, hlam]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, h2476, hc12, hlam, hphi, ht01, ht0b, ht5b, p2698_1, u5ehi1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2474, hlam, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2477, hlam, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2480, hlam, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2629, hlam, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2475, hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2478, hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2474, h2662, h2695, hc23, hc45, hlam, hphi, ht34, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2662, hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2476, hlam, p2698_0]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h2479, hlam, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, h2474, h2476, h2695, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [h0, h2476, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2698_1]
                    · have p2698_0 := h2698c.1
                      have p2698_1 := h2698c.2.1
                      have p2698_2 := h2698c.2.2.1
                      have p2698_3 := h2698c.2.2.2
                      linarith only [hlam, p2698_0]
                · linarith only [h0, h2476, h2695, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · linarith only [h0, h2476, h2479, hlam]
      · linarith only [h0, h2475, h2478, hlam]
    · linarith only [h0, h2474, h2477, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2732 | h2732
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2733 | h2733
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2734 | h2734
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2735 | h2735
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2736 | h2736
            · linarith only [h2474, h2476, h2736, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2738 | h2738
              · linarith only [h2474, h2476, h2735, h2738, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2740 | h2740
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2741 | h2741
                  · rcases h0bigk with h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c | h2742c
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h0, hlam, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2476, hlam, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h0, h2474, h2740, h2741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      rcases p2742_3 (m.d 0 1) (by simp) with h2751 | h2751
                      · linarith only [h0, h2751, hlam]
                      · linarith only [h2475, h2751, hlam]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h0, h2474, h2476, h2740, h2741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2474, hlam, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2732, hlam, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2474, h2476, h2733, h2741, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2736, hlam, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2475, hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2733, hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2735, hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2738, hlam, p2742_0]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2736, hc01, hc35, hlam, hphi, ht12, ht23, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2734, hlam, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2738, hc03, hc45, hlam, hphi, ht34, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [h2733, h2738, h2741, hc34, hc45, hlam, hphi, p2742_1]
                    · have p2742_0 := h2742c.1
                      have p2742_1 := h2742c.2.1
                      have p2742_2 := h2742c.2.2.1
                      have p2742_3 := h2742c.2.2.2
                      linarith only [hlam, p2742_0]
                  · linarith only [h2735, h2736, h2741, hc23, hc35, hlam, hphi]
                · linarith only [h0, h2732, h2740, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2772 | h2772
            · linarith only [h2475, h2476, h2735, h2772, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2774 | h2774
              · linarith only [h2475, h2476, h2774, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2776 | h2776
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2777 | h2777
                  · linarith only [h0, h2474, h2735, h2776, h2777, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c | h2779c
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [hlam, p2779_0]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h0, hlam, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h0, h2474, h2776, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2476, hlam, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [hlam, p2779_0]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      rcases p2779_3 (m.d 0 1) (by simp) with h2787 | h2787
                      · linarith only [h0, h2787, hlam]
                      · linarith only [h2474, h2787, hlam]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      rcases p2779_3 (m.d 0 1) (by simp) with h2790 | h2790
                      · linarith only [h0, h2790, hlam]
                      · linarith only [h2475, h2790, hlam]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h0, h2474, h2476, h2776, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2474, hlam, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2732, hlam, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [hlam, p2779_0]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2735, hlam, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2772, hlam, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2475, hlam, p2779_0]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2733, hlam, p2779_0]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2474, h2475, h2476, h2772, h2776, hc23, hc35, hlam, hphi, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [hlam, p2779_0]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2774, hlam, p2779_0]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2772, hc01, hc35, hlam, hphi, ht12, ht23, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2734, hlam, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2474, h2772, h2776, hc23, hc35, hlam, hphi, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [h2774, hc04, hc45, hlam, hphi, p2779_1]
                    · have p2779_0 := h2779c.1
                      have p2779_1 := h2779c.2.1
                      have p2779_2 := h2779c.2.2.1
                      have p2779_3 := h2779c.2.2.2
                      linarith only [hlam, p2779_0]
                · linarith only [h0, h2732, h2776, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2810 | h2810
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2811 | h2811
            · linarith only [h2474, h2476, h2811, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2813 | h2813
              · linarith only [h0, h2474, h2734, h2810, h2813, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2815 | h2815
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2816 | h2816
                  · rcases h0bigk with h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c | h2817c
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h0, hlam, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2476, hlam, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h0, h2474, h2815, h2816, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2475, h2734, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2734, hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2474, hlam, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2732, hlam, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2475, h2811, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2811, hlam, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2475, hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2733, hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2810, hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2813, hlam, p2817_0]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2734, hc01, hc25, hlam, hphi, ht12, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2734, hc02, hc25, hlam, hphi, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2811, hc03, hc35, hlam, hphi, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [h2475, h2813, hc14, hc45, hlam, hphi, p2817_1]
                    · have p2817_0 := h2817c.1
                      have p2817_1 := h2817c.2.1
                      have p2817_2 := h2817c.2.2.1
                      have p2817_3 := h2817c.2.2.2
                      linarith only [hlam, p2817_0]
                  · linarith only [h2810, h2811, h2816, hc23, hc35, hlam, hphi]
                · linarith only [h0, h2732, h2815, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2845 | h2845
            · linarith only [h2475, h2476, h2810, h2845, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2847 | h2847
              · linarith only [h0, h2475, h2734, h2847, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2849 | h2849
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2850 | h2850
                  · linarith only [h0, h2474, h2810, h2849, h2850, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c | h2852c
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h0, hlam, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h0, h2474, h2734, h2849, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h0, h2734, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2476, hlam, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2734, hc01, hc25, hlam, hphi, ht12, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2474, h2734, h2849, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2475, h2734, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2734, hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2474, hlam, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2732, hlam, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2810, hlam, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2845, hlam, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2475, hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2733, hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h0, h2474, h2475, h2849, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2847, hlam, p2852_0]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2845, hc01, hc35, hlam, hphi, ht12, ht23, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2845, hc02, hc35, hlam, hphi, ht23, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2474, h2845, h2849, hc23, hc35, hlam, hphi, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [h2847, hc04, hc45, hlam, hphi, p2852_1]
                    · have p2852_0 := h2852c.1
                      have p2852_1 := h2852c.2.1
                      have p2852_2 := h2852c.2.2.1
                      have p2852_3 := h2852c.2.2.2
                      linarith only [hlam, p2852_0]
                · linarith only [h0, h2732, h2849, hlam]
      · linarith only [h0, h2475, h2733, hlam]
    · linarith only [h0, h2474, h2732, hlam]

end R2N4
