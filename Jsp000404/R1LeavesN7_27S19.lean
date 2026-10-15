import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3885 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4515 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h4516 | h4516
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4517 | h4517
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4518 | h4518
      · linarith only [h3885, h4515, h4518, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4520 | h4520
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4521 | h4521
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4522 | h4522
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4523 | h4523
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4524 | h4524
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4525 | h4525
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4526 | h4526
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4527 | h4527
                      · rcases h5bigk with h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c | h4528c
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h3355, hlam, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h3355, h4520, h4525, h4527, hc45, hlam, hphi, ht01, ht0b, ht5b, p4528_1, u1elo1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h3355, h4518, h4520, h4524, h4527, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h3355, h4518, h4520, h4524, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4518, h4520, h4524, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4518, h4520, h4524, h4525, h4527, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4518, h4520, h4524, h4527, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4518, h4520, h4524, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4515, hlam, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4520, hlam, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4515, h4527, hc02, hc45, hlam, hphi, ht0b, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h3355, h4515, h4518, h4520, h4524, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4516, hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4522, hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4525, hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4516, hc03, hc45, hlam, hphi, ht0b, ht5b, p4528_1]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4517, hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4523, hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4526, hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [h4527, hlam, p4528_0]
                        · have p4528_0 := h4528c.1
                          have p4528_1 := h4528c.2.1
                          have p4528_2 := h4528c.2.2.1
                          have p4528_3 := h4528c.2.2.2
                          linarith only [hlam, p4528_0]
                      · rcases h5bigk with h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c | h4554c
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h3355, hlam, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h3355, h4518, h4520, h4524, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h3355, h4518, h4520, h4524, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h3355, h4518, h4520, h4524, h4527, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4518, h4520, h4524, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4518, h4520, h4524, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4518, h4520, h4524, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4518, h4520, h4524, h4527, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4515, hlam, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4520, hlam, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h0, h3885, h4515, h4521, hc35, hlam, hphi, ht01, ht0b, ht5b, p4554_1, u1elo2]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h0, h3885, h4515, h4521, h4527, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4554_1, u1elo2]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4516, hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4522, hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4525, hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4527, hlam, p4554_1]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4517, hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4523, hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h4526, hlam, p4554_0]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [h0, h4517, h4521, hc35, hlam, hphi, ht01, ht0b, ht5b, p4554_1, u1elo2]
                        · have p4554_0 := h4554c.1
                          have p4554_1 := h4554c.2.1
                          have p4554_2 := h4554c.2.2.1
                          have p4554_3 := h4554c.2.2.2
                          linarith only [hlam, p4554_0]
                    · linarith only [h3355, h4518, h4520, h4526, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h3885, h4515, h4516, h4524, h4525, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h3355, h4518, h4520, h4521, h4524, hc01, hlam, hphi, u1elo2]
              · linarith only [h0, h4517, h4523, hlam]
            · linarith only [h0, h3355, h4516, h4520, h4521, h4522, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4585 | h4585
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4586 | h4586
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4587 | h4587
                · linarith only [h3355, h4521, h4585, h4587, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4589 | h4589
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4590 | h4590
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4591 | h4591
                      · rcases h5bigk with h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c | h4592c
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h3355, hlam, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h3355, h4520, h4589, h4591, hc45, hlam, hphi, ht01, ht0b, ht5b, p4592_1, u1elo1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h0, h3885, h4515, h4591, hc45, hlam, hphi, ht01, ht0b, ht5b, p4592_1, u1elo3]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h3355, h4518, h4520, h4587, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4518, h4520, h4587, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4518, h4520, h4587, h4589, h4591, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4518, h4520, h4587, h4591, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4518, h4520, h4587, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4515, hlam, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4520, hlam, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h3885, h4515, h4587, h4591, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h3355, h4515, h4518, h4520, h4587, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4516, hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4585, hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4589, hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4516, hc03, hc45, hlam, hphi, ht0b, ht5b, p4592_1]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4517, hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4586, hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4590, hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [h4591, hlam, p4592_0]
                        · have p4592_0 := h4592c.1
                          have p4592_1 := h4592c.2.1
                          have p4592_2 := h4592c.2.2.1
                          have p4592_3 := h4592c.2.2.2
                          linarith only [hlam, p4592_0]
                      · linarith only [h3355, h4518, h4520, h4587, h4591, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h3355, h4517, h4518, h4520, h4590, hc01, hlam, hphi, u1elo3]
                  · linarith only [h4521, h4585, h4589, hc23, hc34, hlam, hphi]
              · linarith only [h0, h4517, h4586, hlam]
            · linarith only [h3355, h4516, h4585, hlam]
        · linarith only [h3885, h4515, h4520, hc12, hc24, hlam, hphi]
    · linarith only [h3885, h4515, h4517, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4625 | h4625
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4626 | h4626
      · linarith only [h3885, h4515, h4626, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4628 | h4628
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4629 | h4629
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4630 | h4630
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4631 | h4631
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4632 | h4632
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4633 | h4633
                  · linarith only [h4515, h4516, h4633, hlam]
                  · linarith only [h3355, h4626, h4628, h4632, h4633, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h3355, h4626, h4628, h4629, h4632, hc01, hlam, hphi, u1elo2]
              · linarith only [h0, h4625, h4631, hlam]
            · linarith only [h4626, h4628, h4629, h4630, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4639 | h4639
            · linarith only [h4516, h4629, h4639, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4641 | h4641
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4642 | h4642
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4643 | h4643
                  · linarith only [h0, h3355, h3885, h4515, h4639, h4643, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h4629, h4642, h4643, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4646 | h4646
                  · linarith only [h4516, h4642, h4646, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4648 | h4648
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4649 | h4649
                      · rcases h5bigk with h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c | h4650c
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h3355, hlam, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h0, h3885, h4515, h4646, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4650_1, u1elo3]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4516, hlam, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h3355, h4628, hc45, hlam, hphi, ht01, ht0b, ht5b, p4650_1, u1elo1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4628, hc05, hlam, hphi, ht01, ht0b, ht5b, p4650_1, u1elo1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4626, h4628, h4646, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4639, hlam, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4626, h4628, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4515, hlam, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4628, hlam, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4646, hlam, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h3885, h4515, h4642, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4646, hc23, hc35, hlam, hphi, p4650_1]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          rcases p4650_3 (m.d 0 5) (by simp) with h4670 | h4670
                          · linarith only [h4516, h4670, hlam]
                          · linarith only [h4625, h4670, hlam]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4625, hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4641, hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4648, hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [h4649, hlam, p4650_0]
                        · have p4650_0 := h4650c.1
                          have p4650_1 := h4650c.2.1
                          have p4650_2 := h4650c.2.2.1
                          have p4650_3 := h4650c.2.2.2
                          linarith only [hlam, p4650_0]
                      · linarith only [h3885, h4515, h4642, h4646, h4649, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h3885, h4515, h4646, h4648, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h3355, h4625, h4628, h4641, hc01, hlam, hphi, u1elo1]
        · linarith only [h3885, h4515, h4628, hc12, hc24, hlam, hphi]
    · linarith only [h3885, h4515, h4625, hlam]

set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3885 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4515 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4683 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h4684 | h4684
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4685 | h4685
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4686 | h4686
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4687 | h4687
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4688 | h4688
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4689 | h4689
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4690 | h4690
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4691 | h4691
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4692 | h4692
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4693 | h4693
                    · rcases h5bigk with h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h3355, hlam, p4694_1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4515, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h3885, h4684, h4685, h4693, hc45, hlam, hphi, ht01, ht0b, ht5b, p4694_1, u1elo1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h3885, h4684, h4685, hc45, hlam, hphi, ht01, ht0b, ht5b, p4694_1, u1elo1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p4694_1, u1elo4]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4515, h4686, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4694_1, u1elo1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4686, h4693, hc45, hlam, hphi, ht01, ht0b, ht5b, p4694_1, u1elo1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4689, hc45, hlam, hphi, ht01, ht0b, ht5b, p4694_1, u1elo3]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p4694_1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4686, hlam, p4694_1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4686, h4693, hc45, hlam, hphi, ht01, ht0b, ht5b, p4694_1, u1elo1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4685, h4692, hc45, hlam, hphi, ht01, ht0b, ht5b, p4694_1, u1elo1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4683, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4688, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4691, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht0b, ht5b, p4694_1]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4684, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4689, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4692, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [h4693, hlam, p4694_0]
                      · have p4694_0 := h4694c.1
                        have p4694_1 := h4694c.2.1
                        have p4694_2 := h4694c.2.2.1
                        have p4694_3 := h4694c.2.2.2
                        linarith only [hlam, p4694_0]
                    · linarith only [h3885, h4684, h4685, h4693, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h3885, h4684, h4692, hlam]
                · linarith only [h3885, h4683, h4684, h4685, h4690, h4691, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4723 | h4723
                · linarith only [h4687, h4690, h4723, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h4515, h4683, h4723, hlam]
            · linarith only [h3885, h4684, h4685, h4689, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · linarith only [h3885, h4683, h4684, h4685, h4687, h4688, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4728 | h4728
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4729 | h4729
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4730 | h4730
              · linarith only [h3355, h4687, h4728, h4730, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4732 | h4732
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4733 | h4733
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4734 | h4734
                    · rcases h5bigk with h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c | h4735c
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h3355, hlam, p4735_1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4515, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4515, h4685, h4730, h4732, hc35, hlam, hphi, ht01, ht0b, ht5b, p4735_1, u1elo1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4515, h4685, h4730, h4732, hc45, hlam, hphi, ht01, ht0b, ht5b, p4735_1, u1elo1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4728, hc05, hlam, hphi, ht01, ht0b, ht5b, p4735_1, u1elo2]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4515, h4687, h4728, hc02, hc34, hlam, hphi, ht23, p4735_1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4515, h4685, h4687, h4728, h4730, h4732, h4734, hc02, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p4735_1, u1elo1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4515, h4685, h4687, h4728, h4730, h4732, hc02, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p4735_1, u1elo1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h3355, h4685, h4730, h4732, hc01, hlam, hphi, p4735_1, u1elo1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4686, hlam, p4735_1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4685, h4730, h4732, h4734, hc45, hlam, hphi, ht01, ht0b, ht5b, p4735_1, u1elo1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4685, h4730, h4732, hc45, hlam, hphi, ht01, ht0b, ht5b, p4735_1, u1elo1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4683, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4728, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4732, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht0b, ht5b, p4735_1]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4684, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4729, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4733, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [h4734, hlam, p4735_0]
                      · have p4735_0 := h4735c.1
                        have p4735_1 := h4735c.2.1
                        have p4735_2 := h4735c.2.2.1
                        have p4735_3 := h4735c.2.2.2
                        linarith only [hlam, p4735_0]
                    · linarith only [h3355, h4515, h4685, h4687, h4728, h4730, h4732, h4734, hc01, hc02, hc45, hlam, hphi, ht23, ht34, u1elo1]
                  · linarith only [h3885, h4684, h4733, hlam]
                · linarith only [h4687, h4728, h4732, hc23, hc34, hlam, hphi]
            · linarith only [h3885, h4684, h4685, h4729, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · linarith only [h3355, h3885, h4683, h4684, h4685, h4728, hc01, hlam, hphi, u1elo1]
      · linarith only [h3885, h4685, h4686, hc02, hc25, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4767 | h4767
      · linarith only [h4515, h4685, h4767, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4769 | h4769
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4770 | h4770
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4771 | h4771
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4772 | h4772
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4773 | h4773
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4774 | h4774
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4775 | h4775
                    · rcases h5bigk with h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c | h4776c
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h3355, hlam, p4776_1]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4515, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h3355, h4769, h4771, h4775, hc45, hlam, hphi, ht01, ht0b, ht5b, p4776_1, u1elo2]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h3355, h4769, h4771, hc45, hlam, hphi, ht01, ht0b, ht5b, p4776_1, u1elo2]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4769, h4771, hc05, hlam, hphi, ht01, ht0b, ht5b, p4776_1, u1elo2]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4767, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4769, h4771, h4775, hc45, hlam, hphi, ht01, ht0b, ht5b, p4776_1, u1elo2]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4769, h4771, hc45, hlam, hphi, ht01, ht0b, ht5b, p4776_1, u1elo2]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p4776_1]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4767, hc12, hc25, hlam, hphi, p4776_1]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        rcases p4776_3 (m.d 0 5) (by simp) with h4790 | h4790
                        · linarith only [h4515, h4790, hlam]
                        · linarith only [h4683, h4790, hlam]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        rcases p4776_3 (m.d 0 5) (by simp) with h4793 | h4793
                        · linarith only [h4515, h4793, hlam]
                        · linarith only [h4684, h4793, hlam]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4683, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4770, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4773, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht0b, ht5b, p4776_1]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4684, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4771, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4774, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [h4775, hlam, p4776_0]
                      · have p4776_0 := h4776c.1
                        have p4776_1 := h4776c.2.1
                        have p4776_2 := h4776c.2.2.1
                        have p4776_3 := h4776c.2.2.2
                        linarith only [hlam, p4776_0]
                    · rcases h5bigk with h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c | h4806c
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h3355, hlam, p4806_1]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4515, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h3355, hc35, hlam, hphi, ht01, ht0b, ht5b, p4806_1, u1elo4]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h0, h4684, h4769, h4775, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4806_1, u1elo2]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p4806_1, u1elo4]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4767, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4770, hc35, hlam, hphi, ht01, ht0b, ht5b, p4806_1, u1elo2]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4769, h4771, h4775, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4806_1, u1elo2]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4684, h4772, h4774, h4775, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4806_1]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h3355, h4772, h4774, hc01, hc23, hlam, hphi, ht12, p4806_1]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        rcases p4806_3 (m.d 0 5) (by simp) with h4820 | h4820
                        · linarith only [h4515, h4820, hlam]
                        · linarith only [h4683, h4820, hlam]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4772, h4774, h4775, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4806_1]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4683, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4770, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4773, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4775, hlam, p4806_1]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4684, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4771, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4774, hlam, p4806_0]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [h4775, hc34, hc45, hlam, hphi, p4806_1]
                      · have p4806_0 := h4806c.1
                        have p4806_1 := h4806c.2.1
                        have p4806_2 := h4806c.2.2.1
                        have p4806_3 := h4806c.2.2.2
                        linarith only [hlam, p4806_0]
                  · linarith only [h0, h3885, h4684, h4769, h4774, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h4770, h4772, h4773, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h0, h4685, h4769, h4772, hc01, hlam, hphi, u1elo2]
            · linarith only [h0, h4684, h4771, hlam]
          · linarith only [h0, h4683, h4684, h4769, h4770, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4839 | h4839
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4840 | h4840
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4841 | h4841
              · linarith only [h3355, h4769, h4839, h4841, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4843 | h4843
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4844 | h4844
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4845 | h4845
                    · rcases h5bigk with h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c | h4846c
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h3355, hlam, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4515, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h3355, h4767, h4841, h4843, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h3355, h4767, h4841, h4843, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4767, h4841, h4843, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4767, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4767, h4841, h4843, h4845, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4767, h4841, h4843, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h3355, h4841, h4843, hc01, hc34, hlam, hphi, ht12, ht23, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4841, h4843, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4841, h4843, h4845, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4841, h4843, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4683, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4839, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4843, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht0b, ht5b, p4846_1]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4684, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4840, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4844, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [h4845, hlam, p4846_0]
                      · have p4846_0 := h4846c.1
                        have p4846_1 := h4846c.2.1
                        have p4846_2 := h4846c.2.2.1
                        have p4846_3 := h4846c.2.2.2
                        linarith only [hlam, p4846_0]
                    · linarith only [h4515, h4841, h4843, h4845, hc02, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h3355, h4684, h4685, h4839, h4844, hc01, hlam, hphi, u1elo2]
                · linarith only [h4769, h4839, h4843, hc23, hc34, hlam, hphi]
            · linarith only [h0, h4684, h4840, hlam]
          · linarith only [h3355, h4683, h4839, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4877 | h4877
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4878 | h4878
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4879 | h4879
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4880 | h4880
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4881 | h4881
            · linarith only [h0, h4684, h4877, h4881, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4883 | h4883
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4884 | h4884
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4885 | h4885
                  · linarith only [h4877, h4881, h4885, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4887 | h4887
                    · linarith only [h0, h4881, h4887, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h5bigk with h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c | h4889c
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h3355, hlam, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4515, hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4515, h4878, h4887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4889_1, u1elo1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4684, hlam, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p4889_1, u1elo4]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h3885, h4878, h4885, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4889_1, u1elo1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4878, h4887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4889_1, u1elo1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4881, hlam, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h0, h4684, hc01, hc25, hlam, hphi, ht12, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4878, hlam, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4878, h4887, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4889_1, u1elo1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4885, hlam, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4683, hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4880, hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4884, hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [hlam, p4889_0]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4887, hlam, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h0, h4684, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4515, hc02, hc45, hlam, hphi, ht23, ht34, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [h4887, hc34, hc45, hlam, hphi, p4889_1]
                      · have p4889_0 := h4889c.1
                        have p4889_1 := h4889c.2.1
                        have p4889_2 := h4889c.2.2.1
                        have p4889_3 := h4889c.2.2.2
                        linarith only [hlam, p4889_0]
                · linarith only [h4515, h4683, h4878, h4883, h4884, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4916 | h4916
                · linarith only [h4879, h4883, h4916, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h4515, h4683, h4916, hlam]
          · linarith only [h4515, h4683, h4878, h4879, h4880, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4920 | h4920
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4921 | h4921
            · linarith only [h0, h4684, h4921, hc01, hlam, hphi, u1elo3]
            · linarith only [h4879, h4920, h4921, hlam]
          · linarith only [h3355, h4515, h4683, h4878, h4920, hc01, hlam, hphi, u1elo1]
      · linarith only [h3885, h4877, h4878, hc02, hc25, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4926 | h4926
      · linarith only [h4515, h4877, h4926, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4928 | h4928
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4929 | h4929
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4930 | h4930
            · linarith only [h0, h4684, h4930, hc01, hlam, hphi, u1elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4932 | h4932
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4933 | h4933
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4934 | h4934
                  · linarith only [h0, h4930, h4932, h4934, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4936 | h4936
                    · linarith only [h4877, h4934, h4936, hc12, hc34, hlam, hphi, ht23]
                    · rcases h5bigk with h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h3355, hlam, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4515, hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h3355, h4929, h4936, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4938_1, u1elo2]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4684, hlam, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4929, hc05, hlam, hphi, ht01, ht0b, ht5b, p4938_1, u1elo2]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4926, hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4929, h4936, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4938_1, u1elo2]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4930, hlam, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h0, h4684, hc01, hc25, hlam, hphi, ht12, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4934, h4936, hc34, hc45, hlam, hphi, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4934, hlam, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4683, hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4929, hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4933, hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [hlam, p4938_0]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4936, hlam, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h0, h4684, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h0, h4930, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4515, hc02, hc45, hlam, hphi, ht23, ht34, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [h4936, hc34, hc45, hlam, hphi, p4938_1]
                      · have p4938_0 := h4938c.1
                        have p4938_1 := h4938c.2.1
                        have p4938_2 := h4938c.2.2.1
                        have p4938_3 := h4938c.2.2.2
                        linarith only [hlam, p4938_0]
                · linarith only [h4929, h4932, h4933, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h0, h4877, h4928, h4932, hc01, hlam, hphi, u1elo2]
          · linarith only [h0, h3355, h4683, h4928, h4929, hc01, hlam, hphi, u1elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4967 | h4967
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4968 | h4968
            · linarith only [h0, h4684, h4968, hc01, hlam, hphi, u1elo3]
            · linarith only [h4928, h4967, h4968, hlam]
          · linarith only [h3355, h4683, h4967, hlam]

end R2N4
