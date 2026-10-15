import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_71S11

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_14_H_I_L_R_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h478 | h478
  · rcases m.htr 0 2 4 (by decide) (by decide) with h479 | h479
    · rcases m.htr 0 2 5 (by decide) (by decide) with h480 | h480
      · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
        · rcases m.htr 1 2 4 (by decide) (by decide) with h482 | h482
          · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
            · rcases m.htr 2 4 5 (by decide) (by decide) with h484 | h484
              · rcases h2bigk with h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, hlam, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h483, h484, hc02, hlam, hphi, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h483, h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h478, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h481, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h478, h484, hc02, hlam, hphi, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, h478, h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h479, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h482, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h483, hlam, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h479, h484, hc04, hlam, hphi, ht0b, ht45, ht5b, p485_1, u4ehi4]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h480, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, h479, h480, hc05, hlam, hphi, ht0b, ht45, ht5b, p485_1, u4ehi0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h483, h484, hlam, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h484, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
              · rcases h2bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, hlam, p511_1]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, h483, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi2]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi2]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi2]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p511_1]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h483, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi2]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi2]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h483, h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi3]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h478, hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h481, hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h478, h483, hc02, hlam, hphi, ht0b, ht45, ht5b, p511_1, u4ehi3]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, h478, h483, h484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi3]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h479, hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h482, hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h483, hlam, p511_1]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h484, hlam, p511_1]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h480, hlam, p511_0]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, hc02, hc25, hlam, hphi, p511_1]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h480, h483, hc02, hlam, hphi, ht0b, ht45, ht5b, p511_1, u4ehi3]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [h0, h480, h483, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u4ehi3]
                · have p511_0 := h511c.1
                  have p511_1 := h511c.2.1
                  have p511_2 := h511c.2.2.1
                  have p511_3 := h511c.2.2.2
                  linarith only [hlam, p511_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h537 | h537
              · rcases h2bigk with h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c | h538c
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h0, hlam, p538_1]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  rcases p538_3 (m.d 0 2) (by simp) with h541 | h541
                  · rcases p538_3 (m.d 1 2) (by simp) with h542 | h542
                    · rcases p538_3 (m.d 2 3) (by simp) with h543 | h543
                      · linarith only [h543, hlam, p538_0]
                      · rcases p538_3 (m.d 2 4) (by simp) with h545 | h545
                        · linarith only [h479, h545, hlam]
                        · linarith only [h483, h545, hlam]
                    · linarith only [h481, h542, hlam]
                  · linarith only [h541, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h0, h537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1, u4ehi4]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h0, h537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1, u4ehi4]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p538_1]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  rcases p538_3 (m.d 0 2) (by simp) with h554 | h554
                  · linarith only [h0, h554, hlam]
                  · linarith only [h478, h554, hlam]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1, u4ehi4]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1, u4ehi4]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h478, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h481, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h483, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h478, h537, hc03, hlam, hphi, ht0b, ht45, ht5b, p538_1, u4ehi4]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h479, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h482, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h479, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p538_1]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h0, h479, h537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p538_1, u4ehi4]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h480, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h0, hc02, hc25, hlam, hphi, p538_1]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h479, h537, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p538_1]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [h537, hlam, p538_0]
                · have p538_0 := h538c.1
                  have p538_1 := h538c.2.1
                  have p538_2 := h538c.2.2.1
                  have p538_3 := h538c.2.2.2
                  linarith only [hlam, p538_0]
              · rcases h2bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h0, hlam, p574_1]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  rcases p574_3 (m.d 0 2) (by simp) with h577 | h577
                  · rcases p574_3 (m.d 1 2) (by simp) with h578 | h578
                    · rcases p574_3 (m.d 2 3) (by simp) with h579 | h579
                      · linarith only [h579, hlam, p574_0]
                      · rcases p574_3 (m.d 2 4) (by simp) with h581 | h581
                        · linarith only [h479, h581, hlam]
                        · linarith only [h483, h581, hlam]
                    · linarith only [h481, h578, hlam]
                  · linarith only [h577, hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi2]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h0, h537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi2]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p574_1]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  rcases p574_3 (m.d 0 2) (by simp) with h590 | h590
                  · linarith only [h0, h590, hlam]
                  · linarith only [h478, h590, hlam]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi2]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi2]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h478, hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h481, hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h483, hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h537, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p574_1, u4ehi2]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h479, hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h482, hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h480, h537, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p574_1]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h537, hlam, p574_1]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h480, hlam, p574_0]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h0, h480, hlam, p574_1]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h0, h480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p574_1]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [h0, h480, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p574_1, u4ehi2]
                · have p574_0 := h574c.1
                  have p574_1 := h574c.2.1
                  have p574_2 := h574c.2.2.1
                  have p574_3 := h574c.2.2.2
                  linarith only [hlam, p574_0]
          · linarith only [h0, h479, h482, hlam]
        · linarith only [h0, h478, h481, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
        · rcases m.htr 1 2 4 (by decide) (by decide) with h613 | h613
          · rcases m.htr 2 3 4 (by decide) (by decide) with h614 | h614
            · linarith only [h478, h480, h614, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h616 | h616
              · linarith only [h479, h480, h616, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h479, h480, h616, hc45, hlam, hphi, u4ehi2]
          · linarith only [h0, h479, h613, hlam]
        · linarith only [h0, h478, h612, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h621 | h621
      · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
        · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
          · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
            · linarith only [h478, h479, h623, h624, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h626 | h626
              · linarith only [h479, h621, h623, h626, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h478, h479, h626, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h629 | h629
            · linarith only [h0, h478, h623, h629, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h631 | h631
              · rcases h2bigk with h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h0, hlam, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h0, h623, h629, hc23, hc34, hlam, hphi, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h479, hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h0, h623, h629, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h623, h629, hc02, hc34, hlam, hphi, ht23, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h623, h629, hc23, hc34, hlam, hphi, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h623, hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h623, h629, h631, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p632_1, u4ehi4]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h478, hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h622, hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h629, hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h631, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p632_1, u4ehi4]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h621, h629, h631, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p632_1, u4ehi4]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h629, hc12, hc34, hlam, hphi, ht23, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h629, hc23, hc34, hlam, hphi, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h629, h631, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p632_1, u4ehi4]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h621, hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h0, h621, hlam, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h621, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p632_1]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [h631, hlam, p632_0]
                · have p632_0 := h632c.1
                  have p632_1 := h632c.2.1
                  have p632_2 := h632c.2.2.1
                  have p632_3 := h632c.2.2.2
                  linarith only [hlam, p632_0]
              · linarith only [h0, h623, h631, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h478, h622, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h660 | h660
        · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
          · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
            · linarith only [h478, h479, h661, h662, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h664 | h664
              · rcases h2bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h0, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h621, h661, h664, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h479, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h621, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  rcases p665_3 (m.d 0 2) (by simp) with h673 | h673
                  · linarith only [h0, h673, hlam]
                  · linarith only [h478, h673, hlam]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p665_1, u4ehi2]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h478, h621, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h478, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h660, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h662, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h478, h621, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h478, h661, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h661, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h478, h621, h661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h478, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h661, h664, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h661, h664, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h664, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
              · linarith only [h478, h479, h664, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h694 | h694
            · linarith only [h0, h478, h661, h694, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h696 | h696
              · rcases h2bigk with h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c | h697c
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h0, hlam, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h0, h661, h694, hc23, hc34, hlam, hphi, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h479, hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h621, hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h661, h694, hc02, hc34, hlam, hphi, ht23, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h661, h694, hc23, hc34, hlam, hphi, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h661, hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h478, h621, h661, h694, hc23, hc34, hlam, hphi, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h478, hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h660, hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h694, hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h478, h621, hlam, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h478, h694, hc23, hc34, hlam, hphi, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h694, hc12, hc34, hlam, hphi, ht23, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h694, hc23, hc34, hlam, hphi, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h478, h621, h694, hc23, hc34, hlam, hphi, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h478, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h0, h694, h696, hc01, hc34, hlam, hphi, ht12, ht23, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h694, h696, hc23, hc34, hlam, hphi, p697_1]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [h696, hlam, p697_0]
                · have p697_0 := h697c.1
                  have p697_1 := h697c.2.1
                  have p697_2 := h697c.2.2.1
                  have p697_3 := h697c.2.2.2
                  linarith only [hlam, p697_0]
              · linarith only [h478, h479, h696, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h478, h479, h660, hc01, hc24, hlam, hphi, ht12]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h725 | h725
    · rcases m.htr 0 2 5 (by decide) (by decide) with h726 | h726
      · rcases m.htr 1 2 3 (by decide) (by decide) with h727 | h727
        · linarith only [h478, h725, h727, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h729 | h729
          · rcases m.htr 2 3 4 (by decide) (by decide) with h730 | h730
            · rcases m.htr 2 4 5 (by decide) (by decide) with h731 | h731
              · linarith only [h0, h725, h727, h731, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases h2bigk with h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c | h733c
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h0, hlam, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h478, hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h0, h727, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p733_1, u4ehi2]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h0, h727, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h727, hc02, hc23, hlam, hphi, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h727, hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h727, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p733_1, u4ehi2]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h727, h730, h731, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p733_1, u4ehi3]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h726, h730, h731, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p733_1, u4ehi3]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h730, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p733_1, u4ehi3]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h730, h731, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p733_1, u4ehi3]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h725, hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h729, hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h730, hlam, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h731, hlam, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h726, hlam, p733_0]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h0, h726, hlam, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h726, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p733_1]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [h0, h726, h727, h730, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p733_1, u4ehi3]
                · have p733_0 := h733c.1
                  have p733_1 := h733c.2.1
                  have p733_2 := h733c.2.2.1
                  have p733_3 := h733c.2.2.2
                  linarith only [hlam, p733_0]
            · linarith only [h0, h727, h730, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h0, h725, h729, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h761 | h761
        · linarith only [h478, h725, h761, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h763 | h763
          · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
            · rcases m.htr 2 4 5 (by decide) (by decide) with h765 | h765
              · linarith only [h0, h725, h761, h765, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h725, h726, h765, hc45, hlam, hphi, u4ehi2]
            · linarith only [h0, h761, h764, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h0, h725, h763, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h770 | h770
      · rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
        · rcases m.htr 1 2 4 (by decide) (by decide) with h772 | h772
          · rcases m.htr 2 3 4 (by decide) (by decide) with h773 | h773
            · rcases m.htr 2 4 5 (by decide) (by decide) with h774 | h774
              · linarith only [h725, h770, h771, h773, h774, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h725, h770, h774, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h777 | h777
              · linarith only [h478, h770, h773, h777, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h478, h770, h773, h777, hlam]
          · linarith only [h478, h770, h771, h772, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h781 | h781
          · linarith only [h725, h770, h771, h781, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h783 | h783
            · rcases m.htr 2 4 5 (by decide) (by decide) with h784 | h784
              · rcases h2bigk with h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h0, hlam, p785_1]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h478, hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h725, hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h784, hc02, hlam, hphi, ht0b, ht45, ht5b, p785_1, u4ehi4]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h781, h783, hc02, hc23, hlam, hphi, p785_1]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h771, hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h781, hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h781, h783, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u4ehi4]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h770, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u4ehi4]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p785_1]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u4ehi2]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u4ehi4]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h770, h784, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u4ehi4]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h0, h770, h784, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u4ehi4]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h783, hlam, p785_1]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h783, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1, u4ehi4]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h770, hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h0, h770, hlam, p785_1]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h478, h770, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p785_1]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [h784, hlam, p785_0]
                · have p785_0 := h785c.1
                  have p785_1 := h785c.2.1
                  have p785_2 := h785c.2.2.1
                  have p785_3 := h785c.2.2.2
                  linarith only [hlam, p785_0]
              · linarith only [h0, h781, h784, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h771, h783, hc01, hc34, hlam, hphi, ht12, ht23]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h813 | h813
        · rcases m.htr 1 2 4 (by decide) (by decide) with h814 | h814
          · rcases m.htr 2 3 4 (by decide) (by decide) with h815 | h815
            · rcases m.htr 2 4 5 (by decide) (by decide) with h816 | h816
              · rcases h2bigk with h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c | h817c
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, hlam, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h478, hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h725, hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h770, hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h815, h816, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p817_1, u4ehi4]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h816, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p817_1, u4ehi4]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, h770, hc01, hc12, hlam, hphi, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h813, hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h813, h816, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p817_1, u4ehi4]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, h770, h813, hc01, hc12, hlam, hphi, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h814, hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h815, hlam, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, h770, h813, h815, hc01, hc12, hlam, hphi, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h813, h815, h816, hlam, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h815, h816, hlam, p817_1]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [h816, hlam, p817_0]
                · have p817_0 := h817c.1
                  have p817_1 := h817c.2.1
                  have p817_2 := h817c.2.2.1
                  have p817_3 := h817c.2.2.2
                  linarith only [hlam, p817_0]
              · rcases h2bigk with h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c | h843c
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, hlam, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h478, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h725, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h770, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h478, hc01, hc12, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h725, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p843_1, u4ehi0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h770, hc01, hc12, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h813, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h725, h813, hc01, hc12, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h725, h813, h816, hc01, hc12, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, h814, hc01, hc14, hlam, hphi, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h814, hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h815, hlam, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h816, hlam, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h816, hc12, hc45, hlam, hphi, ht23, ht34, p843_1]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h815, h816, hc45, hlam, hphi, p843_1, u4ehi3]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [h816, hc45, hlam, hphi, p843_1, u4ehi2]
                · have p843_0 := h843c.1
                  have p843_1 := h843c.2.1
                  have p843_2 := h843c.2.2.1
                  have p843_3 := h843c.2.2.2
                  linarith only [hlam, p843_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h869 | h869
              · rcases h2bigk with h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h478, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h725, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h770, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h478, hc01, hc12, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h869, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p870_1, u4ehi4]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h770, hc01, hc12, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h813, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h815, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h770, h814, h815, hc01, hc14, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h814, hc01, hc14, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h814, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h478, h814, hc01, hc14, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h770, h814, hc01, hc12, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h814, h869, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h478, h814, h869, hc01, hc12, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h869, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
              · rcases h2bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, hlam, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h478, hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h725, hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h770, hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, h478, hc01, hc12, hlam, hphi, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p896_1, u4ehi2]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, h770, hc01, hc12, hlam, hphi, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h813, hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h815, hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h815, h869, hlam, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, h869, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h814, hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h869, hc23, hc45, hlam, hphi, ht34, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [hlam, p896_0]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h869, hlam, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h869, hc12, hc45, hlam, hphi, ht23, ht34, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, h478, h869, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [h0, h478, h815, h869, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p896_1]
                · have p896_0 := h896c.1
                  have p896_1 := h896c.2.1
                  have p896_2 := h896c.2.2.1
                  have p896_3 := h896c.2.2.2
                  linarith only [hlam, p896_0]
          · linarith only [h0, h478, h813, h814, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
          · linarith only [h0, h725, h813, h923, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h925 | h925
            · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
              · rcases h2bigk with h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, hlam, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h478, hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h725, hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h770, hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, h923, h925, hc01, hc23, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h813, hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h923, hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h923, h925, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p927_1, u4ehi2]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, h770, hc01, hc23, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h925, hlam, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, h770, h925, hc01, hc23, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h0, h925, h926, hc01, hc23, hlam, hphi, ht12, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h925, h926, hlam, p927_1]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [h926, hlam, p927_0]
                · have p927_0 := h927c.1
                  have p927_1 := h927c.2.1
                  have p927_2 := h927c.2.2.1
                  have p927_3 := h927c.2.2.2
                  linarith only [hlam, p927_0]
              · linarith only [h0, h923, h926, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h813, h925, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_22_14_H_I_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_14_H_I_L_R_x0 m hb2 hb4 h0
  · exact r1l7_22_14_H_I_L_R_x1 m hb2 hb4 h0

end R2N4
