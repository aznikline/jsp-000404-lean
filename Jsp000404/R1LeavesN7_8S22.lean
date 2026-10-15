import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S19
import Jsp000404.R1LeavesN7_8S20
import Jsp000404.R1LeavesN7_8S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14268 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14663 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h14791 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 3 5 (by decide) (by decide) with h15455 | h15455
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15456 | h15456
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15457 | h15457
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15458 | h15458
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15459 | h15459
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15460 | h15460
            · linarith only [h14791, h15455, h15460, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15462 | h15462
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15463 | h15463
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15464 | h15464
                  · linarith only [h15460, h15464, h7600, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15466 | h15466
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15467 | h15467
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15468 | h15468
                        · rcases h0bigk with h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c | h15469c
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h0, hlam, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h7600, hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h8836, hlam, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h9666, hlam, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h15457, h9886, hc01, hc13, hlam, hphi, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h9886, hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h14268, hlam, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h14663, hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h15457, h15460, h9886, hc01, hc34, hlam, hphi, ht12, ht23, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h15457, h15460, h9886, hc02, hc34, hlam, hphi, ht23, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h14791, hlam, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h15457, h15460, h9886, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p15469_1, u5ehi0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h14268, h15458, hc01, hc12, hlam, hphi, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h0, h14268, h15458, hc01, hc12, hlam, hphi, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h14268, h15455, h15458, hc12, hlam, hphi, ht01, ht0b, ht5b, p15469_1, u5ehi3]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h14268, h15455, h15458, h15468, hc12, hlam, hphi, ht01, ht0b, ht5b, p15469_1, u5ehi4]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h15460, h15462, h9666, hc01, hc34, hlam, hphi, ht12, ht23, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h0, h14663, h15459, h15460, h15462, hc01, hc34, hlam, hphi, ht12, ht23, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h15455, hlam, p15469_0]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [h15456, hlam, p15469_1]
                          · have p15469_0 := h15469c.1
                            have p15469_1 := h15469c.2.1
                            have p15469_2 := h15469c.2.2.1
                            have p15469_3 := h15469c.2.2.2
                            linarith only [hlam, p15469_0]
                        · linarith only [h15460, h15468, h7600, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h14268, h15456, h15467, hlam]
                    · linarith only [h15455, h15466, h9886, hlam]
                · linarith only [h14268, h15456, h15458, h15463, hlam]
              · linarith only [h15455, h15457, h15462, h9886, hlam]
          · linarith only [h14268, h15456, h15458, h15459, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · linarith only [h15455, h15457, h15458, h9886, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15502 | h15502
        · linarith only [h14268, h14791, h15455, h15457, h15502, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15504 | h15504
          · linarith only [h0, h14663, h15457, h15504, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15506 | h15506
            · linarith only [h14791, h15455, h15506, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15508 | h15508
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15509 | h15509
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15510 | h15510
                  · linarith only [h0, h15504, h15506, h15508, h15510, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h15457, h15510, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h15455, h15456, h15506, h15509, h7600, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h15455, h15508, h7600, hlam]
    · linarith only [h14791, h15455, h15456, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15516 | h15516
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15517 | h15517
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15518 | h15518
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15519 | h15519
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15520 | h15520
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15521 | h15521
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15522 | h15522
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15523 | h15523
                  · linarith only [h14791, h15516, h15517, h15523, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · linarith only [h0, h15520, h15523, h9886, hc01, hc13, hlam, hphi]
                · linarith only [h15516, h15522, h8836, hlam]
              · linarith only [h0, h14791, h15520, h15521, h9886, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15528 | h15528
              · linarith only [h0, h15455, h15520, h15528, h9886, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15530 | h15530
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15531 | h15531
                  · linarith only [h14791, h15516, h15517, h15531, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15533 | h15533
                    · linarith only [h15517, h15528, h15533, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15535 | h15535
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15536 | h15536
                        · rcases h0bigk with h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c | h15537c
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [hlam, p15537_0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h0, hlam, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h7600, hlam, p15537_0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h8836, hlam, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h9666, hlam, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h15528, h15536, h7600, h9886, hc01, hc34, hlam, hphi, ht12, ht23, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [hlam, p15537_0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h9886, hlam, p15537_0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h14268, hlam, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h14663, hlam, p15537_0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h15528, h15536, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h15528, h15536, h7600, hc02, hc34, hlam, hphi, ht23, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [hlam, p15537_0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h14791, hlam, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h15455, hlam, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h14268, h15518, hc01, hc12, hlam, hphi, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h0, h14268, h15518, hc01, hc12, hlam, hphi, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h14268, h15518, h7600, hc01, hc12, hlam, hphi, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [hlam, p15537_0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h14268, h15518, hc12, hlam, hphi, ht01, ht0b, ht5b, p15537_1, u5ehi0]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h14268, h15516, h15518, hc01, hc12, hlam, hphi, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h0, h14268, h15516, h15518, hc01, hc12, hlam, hphi, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h0, h14268, h15516, h15518, h9886, hc01, hc12, hlam, hphi, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [h15516, hlam, p15537_1]
                          · have p15537_0 := h15537c.1
                            have p15537_1 := h15537c.2.1
                            have p15537_2 := h15537c.2.2.1
                            have p15537_3 := h15537c.2.2.2
                            linarith only [hlam, p15537_0]
                        · linarith only [h14791, h15516, h15536, hlam]
                      · linarith only [h0, h14268, h15516, h15535, h8836, hc01, hc14, hlam, hphi]
                · linarith only [h14268, h15516, h15518, h15530, h8836, hc01, hc12, hlam, hphi]
          · linarith only [h14268, h15516, h15518, h15519, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · linarith only [h0, h15517, h15518, h9886, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15568 | h15568
        · linarith only [h14268, h15516, h15517, h15568, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15570 | h15570
          · linarith only [h0, h14663, h15517, h15570, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15572 | h15572
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15573 | h15573
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15574 | h15574
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15575 | h15575
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15576 | h15576
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15577 | h15577
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15578 | h15578
                        · rcases h0bigk with h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c | h15579c
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [hlam, p15579_0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h0, hlam, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h7600, hlam, p15579_0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h8836, hlam, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h9666, hlam, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h0, h15570, h15575, h15577, hc01, hc23, hlam, hphi, ht12, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [hlam, p15579_0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h9886, hlam, p15579_0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14268, hlam, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14663, hlam, p15579_0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14791, h15572, hc01, hc13, hlam, hphi, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14791, h15572, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [hlam, p15579_0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14791, hlam, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h15455, hlam, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14791, h15572, hc01, hc13, hlam, hphi, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h0, h14791, h15572, hc01, hc13, hlam, hphi, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14791, h15572, h7600, hc01, hc13, hlam, hphi, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [hlam, p15579_0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h14791, h15572, hc13, hlam, hphi, ht01, ht0b, ht5b, p15579_1, u5ehi0]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h15455, h15572, h15578, hc01, hc13, hlam, hphi, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h0, h15455, h15572, h15578, hc01, hc13, hlam, hphi, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h0, h15455, h15572, h15578, h9886, hc01, hc13, hlam, hphi, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [h15516, hlam, p15579_1]
                          · have p15579_0 := h15579c.1
                            have p15579_1 := h15579c.2.1
                            have p15579_2 := h15579c.2.2.1
                            have p15579_3 := h15579c.2.2.2
                            linarith only [hlam, p15579_0]
                        · linarith only [h14791, h15516, h15578, hlam]
                      · linarith only [h0, h14268, h14791, h15516, h15577, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h14791, h15517, h15572, h15576, h9886, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h15517, h15572, h15575, hlam]
                · linarith only [h14791, h15516, h15572, h15574, h8836, hc01, hc13, hlam, hphi]
              · linarith only [h0, h14791, h15572, h15573, h9886, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15611 | h15611
              · linarith only [h0, h15455, h15572, h15611, h9886, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15613 | h15613
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15614 | h15614
                  · linarith only [h15572, h15614, h7600, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h15517, h15614, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h15516, h15613, h8836, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15618 | h15618
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15619 | h15619
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15620 | h15620
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15621 | h15621
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15622 | h15622
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15623 | h15623
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15624 | h15624
                  · linarith only [h0, h14791, h15618, h15624, h9886, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h15618, h15621, h15624, h9886, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15627 | h15627
                  · linarith only [h0, h14791, h15618, h15627, h9886, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h15618, h15621, h15627, h9886, hc01, hc12, hlam, hphi]
              · linarith only [h0, h14791, h15621, h15622, h9886, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15631 | h15631
              · linarith only [h0, h15455, h15621, h15631, h9886, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15633 | h15633
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15634 | h15634
                  · linarith only [h15621, h15634, h7600, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15636 | h15636
                    · linarith only [h15618, h15631, h15636, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15638 | h15638
                      · linarith only [h0, h14791, h15516, h15619, h15638, h9886, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h14268, h15633, h15638, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15641 | h15641
                  · linarith only [h0, h14791, h15618, h15631, h15641, h9886, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15643 | h15643
                    · linarith only [h0, h15455, h15618, h15643, h9886, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15645 | h15645
                      · linarith only [h15619, h15633, h15645, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15647 | h15647
                        · linarith only [h15621, h15633, h15647, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h15618, h15621, h15647, h9886, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h15618, h15620, h9886, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h15618, h15619, h9886, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15652 | h15652
        · linarith only [h0, h14268, h15618, h15652, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15654 | h15654
          · linarith only [h0, h14663, h15618, h15654, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15656 | h15656
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15657 | h15657
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15658 | h15658
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15659 | h15659
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15660 | h15660
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15661 | h15661
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15662 | h15662
                        · linarith only [h0, h14791, h15516, h15656, h15662, h9886, hc01, hc13, hlam, hphi]
                        · linarith only [h0, h14791, h15658, h15662, h9886, hc01, hc14, hlam, hphi]
                      · linarith only [h15652, h15658, h15661, hlam]
                    · linarith only [h15618, h15657, h15660, hlam]
                  · linarith only [h0, h15455, h15618, h15657, h15659, h9886, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15668 | h15668
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15669 | h15669
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15670 | h15670
                      · linarith only [h15658, h15670, h8836, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h15652, h15670, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h15618, h15657, h15669, hlam]
                  · linarith only [h0, h15455, h15618, h15656, h15657, h15668, h9886, hc01, hc14, hlam, hphi]
              · linarith only [h0, h14791, h15656, h15657, h9886, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15676 | h15676
              · linarith only [h0, h15455, h15656, h15676, h9886, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15678 | h15678
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15679 | h15679
                  · linarith only [h15656, h15679, h7600, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h15618, h15679, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15682 | h15682
                  · linarith only [h15656, h15682, h7600, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h15618, h15682, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14268 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14663 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 3 4 (by decide) (by decide) with h14791 | h14791
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886 h14268 h14663 h14791
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886 h14268 h14663 h14791

set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14268 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 2 5 (by decide) (by decide) with h14663 | h14663
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886 h14268 h14663
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886 h14268 h14663

set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 2 4 (by decide) (by decide) with h14268 | h14268
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886 h14268
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886 h14268

set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 2 3 (by decide) (by decide) with h9886 | h9886
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 h9886

set_option maxHeartbeats 12038000 in
set_option maxHeartbeats 12038000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s12 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  rcases m.htr 0 1 5 (by decide) (by decide) with h9666 | h9666
  · rcases m.htr 0 2 3 (by decide) (by decide) with h9667 | h9667
    · rcases m.htr 0 2 4 (by decide) (by decide) with h9668 | h9668
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9669 | h9669
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9670 | h9670
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9671 | h9671
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9672 | h9672
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9673 | h9673
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9674 | h9674
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9675 | h9675
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9676 | h9676
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9677 | h9677
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9678 | h9678
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9679 | h9679
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9680 | h9680
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9681 | h9681
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9682 | h9682
                                  · linarith only [h9667, h9679, h9682, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h0bigk with h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h0, hlam, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h7600, hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h8836, hlam, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h8836, hc14, hlam, hphi, ht01, ht0b, ht5b, p9684_1, u5ehi0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h0, h9666, h9675, h9681, h9682, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h0, h7600, h9666, h9675, h9681, h9682, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h0, h8836, h9666, h9675, h9681, h9682, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      rcases p9684_3 (m.d 0 1) (by simp) with h9694 | h9694
                                      · linarith only [h0, h9694, hlam]
                                      · linarith only [h9666, h9694, hlam]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9666, h9675, h9681, h9682, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9667, hlam, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h7600, h8836, h9666, h9673, h9675, h9681, h9682, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      rcases p9684_3 (m.d 0 1) (by simp) with h9701 | h9701
                                      · linarith only [h7600, h9701, hlam]
                                      · linarith only [h9666, h9701, hlam]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9666, h9675, h9681, h9682, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9668, hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9670, hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      rcases p9684_3 (m.d 0 1) (by simp) with h9708 | h9708
                                      · linarith only [h8836, h9708, hlam]
                                      · linarith only [h9666, h9708, hlam]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9666, hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9669, hlam, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9671, hlam, p9684_0]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [h9672, hlam, p9684_1]
                                    · have p9684_0 := h9684c.1
                                      have p9684_1 := h9684c.2.1
                                      have p9684_2 := h9684c.2.2.1
                                      have p9684_3 := h9684c.2.2.2
                                      linarith only [hlam, p9684_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9716 | h9716
                                  · linarith only [h0, h9667, h9679, h9681, h9716, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h0, hlam, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h7600, hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h8836, hlam, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h8836, h9673, h9676, hc12, hlam, hphi, ht01, ht0b, ht5b, p9718_1, u5ehi0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h0, h9666, hc12, hlam, hphi, ht01, ht0b, ht5b, p9718_1, u5ehi1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h0, h7600, h9666, hc12, hlam, hphi, ht01, ht0b, ht5b, p9718_1, u5ehi1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h0, h8836, h9666, hc12, hlam, hphi, ht01, ht0b, ht5b, p9718_1, u5ehi1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      rcases p9718_3 (m.d 0 1) (by simp) with h9728 | h9728
                                      · linarith only [h0, h9728, hlam]
                                      · linarith only [h9666, h9728, hlam]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9666, h9678, h9679, h9681, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9667, hlam, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h7600, h8836, h9666, h9673, h9678, h9679, h9681, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      rcases p9718_3 (m.d 0 1) (by simp) with h9735 | h9735
                                      · linarith only [h7600, h9735, hlam]
                                      · linarith only [h9666, h9735, hlam]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9666, h9678, h9679, h9681, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9668, hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9670, hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      rcases p9718_3 (m.d 0 1) (by simp) with h9742 | h9742
                                      · linarith only [h8836, h9742, hlam]
                                      · linarith only [h9666, h9742, hlam]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9666, hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9669, hlam, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9671, hlam, p9718_0]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [h9672, hlam, p9718_1]
                                    · have p9718_0 := h9718c.1
                                      have p9718_1 := h9718c.2.1
                                      have p9718_2 := h9718c.2.2.1
                                      have p9718_3 := h9718c.2.2.2
                                      linarith only [hlam, p9718_0]
                              · linarith only [h8836, h9666, h9673, h9676, h9677, h9679, h9680, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9751 | h9751
                              · linarith only [h7600, h9670, h9673, h9679, h9751, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9753 | h9753
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9754 | h9754
                                  · rcases h0bigk with h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c | h9755c
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h0, hlam, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h7600, hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h8836, hlam, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h8836, h9673, h9676, hc12, hlam, hphi, ht01, ht0b, ht5b, p9755_1, u5ehi0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h0, h9666, hc12, hlam, hphi, ht01, ht0b, ht5b, p9755_1, u5ehi1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h0, h7600, h9666, h9677, h9751, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h0, h8836, h9666, h9677, h9751, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      rcases p9755_3 (m.d 0 1) (by simp) with h9765 | h9765
                                      · linarith only [h0, h9765, hlam]
                                      · linarith only [h9666, h9765, hlam]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9666, h9677, h9751, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9667, hlam, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h7600, h8836, h9666, h9673, h9677, h9751, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      rcases p9755_3 (m.d 0 1) (by simp) with h9772 | h9772
                                      · linarith only [h7600, h9772, hlam]
                                      · linarith only [h9666, h9772, hlam]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9666, h9677, h9751, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9668, hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9670, hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      rcases p9755_3 (m.d 0 1) (by simp) with h9779 | h9779
                                      · linarith only [h8836, h9779, hlam]
                                      · linarith only [h9666, h9779, hlam]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9666, hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9669, hlam, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9671, hlam, p9755_0]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [h9672, hlam, p9755_1]
                                    · have p9755_0 := h9755c.1
                                      have p9755_1 := h9755c.2.1
                                      have p9755_2 := h9755c.2.2.1
                                      have p9755_3 := h9755c.2.2.2
                                      linarith only [hlam, p9755_0]
                                  · linarith only [h9679, h9753, h9754, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9788 | h9788
                                  · rcases h0bigk with h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c | h9789c
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h0, hlam, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h7600, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h8836, hlam, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h8836, h9673, h9676, hc12, hlam, hphi, ht01, ht0b, ht5b, p9789_1, u5ehi0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h0, h9666, h9677, h9679, h9753, h9788, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h0, h7600, h9666, h9677, h9679, h9753, h9788, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h0, h8836, h9666, h9677, h9679, h9753, h9788, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      rcases p9789_3 (m.d 0 1) (by simp) with h9799 | h9799
                                      · linarith only [h0, h9799, hlam]
                                      · linarith only [h9666, h9799, hlam]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9666, h9677, h9679, h9753, h9788, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9667, hlam, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h7600, h8836, h9666, h9673, h9677, h9679, h9753, h9788, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      rcases p9789_3 (m.d 0 1) (by simp) with h9806 | h9806
                                      · linarith only [h7600, h9806, hlam]
                                      · linarith only [h9666, h9806, hlam]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9666, h9677, h9679, h9753, h9788, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9668, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9670, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      rcases p9789_3 (m.d 0 1) (by simp) with h9813 | h9813
                                      · linarith only [h8836, h9813, hlam]
                                      · linarith only [h9666, h9813, hlam]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9666, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9669, hlam, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9671, hlam, p9789_0]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [h9672, hlam, p9789_1]
                                    · have p9789_0 := h9789c.1
                                      have p9789_1 := h9789c.2.1
                                      have p9789_2 := h9789c.2.2.1
                                      have p9789_3 := h9789c.2.2.2
                                      linarith only [hlam, p9789_0]
                                  · linarith only [h8836, h9666, h9673, h9676, h9678, h9679, h9788, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h8836, h9666, h9672, h9678, hc05, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h8836, h9666, h9675, h9676, h9677, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h7600, h9666, h9675, h9676, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h7600, h9666, h9673, h9675, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h7600, h9666, h9673, h9674, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h9666, h9673, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h8836, h9666, h9672, hlam]
            · linarith only [h7600, h9666, h9671, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9830 | h9830
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9831 | h9831
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9832 | h9832
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9833 | h9833
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9834 | h9834
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9835 | h9835
                      · linarith only [h7600, h9666, h9670, h9832, h9834, h9835, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h7600, h9666, h9834, h9835, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h9666, h9834, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h7600, h9666, h9668, h9832, h9833, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h9666, h9667, h9670, h9832, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · linarith only [h7600, h9666, h9670, h9831, hlam]
            · linarith only [h7600, h9666, h9830, hlam]
        · linarith only [h0, h9666, h9669, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9844 | h9844
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9845 | h9845
          · linarith only [h9667, h9668, h9845, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9847 | h9847
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9848 | h9848
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9849 | h9849
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9850 | h9850
                  · linarith only [h7600, h9666, h9667, h9668, h9850, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                  · linarith only [h0, h9666, h9850, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h9666, h9667, h9849, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h9666, h9668, h9848, hlam]
            · linarith only [h7600, h9666, h9847, hlam]
        · linarith only [h7600, h9666, h9667, h9844, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h9857 | h9857
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9858 | h9858
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9859 | h9859
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9860 | h9860
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9861 | h9861
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9862 | h9862
                · linarith only [h9667, h9858, h9862, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h9666, h9862, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h8836, h9666, h9861, hlam]
            · linarith only [h8836, h9666, h9667, h9857, h9860, hlam]
          · linarith only [h9667, h9857, h9859, hlam]
        · linarith only [h8836, h9666, h9857, h9858, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9869 | h9869
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9870 | h9870
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9871 | h9871
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9872 | h9872
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9873 | h9873
                · linarith only [h9667, h9869, h9873, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h9666, h9873, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h9666, h9857, h9872, hlam]
            · linarith only [h0, h9666, h9857, h9870, h9871, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9878 | h9878
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9879 | h9879
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9880 | h9880
                · linarith only [h0, h9666, h9667, h9880, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h9666, h9880, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h7600, h9666, h9870, h9879, hlam]
            · linarith only [h0, h9666, h9667, h9878, hlam]
        · linarith only [h0, h9666, h9869, hlam]
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13 m hb0 hb2 hb3 hb5 h0 h7600 h8836 h9666

end R2N4
