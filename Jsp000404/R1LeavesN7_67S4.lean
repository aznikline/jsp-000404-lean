import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_67S3

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_IR_L_R_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h517 | h517
  · rcases m.htr 0 1 4 (by decide) (by decide) with h518 | h518
    · rcases m.htr 0 1 5 (by decide) (by decide) with h519 | h519
      · rcases m.htr 0 2 3 (by decide) (by decide) with h520 | h520
        · rcases m.htr 0 2 4 (by decide) (by decide) with h521 | h521
          · rcases m.htr 0 2 5 (by decide) (by decide) with h522 | h522
            · rcases m.htr 0 3 4 (by decide) (by decide) with h523 | h523
              · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 0 4 5 (by decide) (by decide) with h525 | h525
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h526 | h526
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h527 | h527
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h528 | h528
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
                          · linarith only [h0, h518, h529, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h517, h523, h525, h527, h529, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h519, h528, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h517, h526, h527, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h519, h526, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h535 | h535
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h538 | h538
                          · linarith only [h0, h518, h525, h538, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h540 | h540
                            · linarith only [h0, h517, h535, h540, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h0, h517, h524, h540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h519, h537, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h517, h535, h536, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h519, h535, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h546 | h546
                  · linarith only [h523, h524, h546, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h550 | h550
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                          · linarith only [h0, h518, h546, h551, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h553 | h553
                            · linarith only [h524, h553, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h555 | h555
                              · linarith only [h0, h519, h546, h549, h551, h555, hc12, hlam, hphi, ht01, u0ehi3]
                              · rcases h0bigk with h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c | h557c
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h0, hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h0, h523, hc12, hlam, hphi, ht01, p557_1, u0ehi3]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p557_1, u0ehi3]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p557_1, u5ehi0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h519, hc02, hlam, hphi, ht0b, ht5b, p557_1, u5ehi1]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h0, h523, hc12, hlam, hphi, ht01, p557_1, u0ehi3]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p557_1, u0ehi3]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p557_1, u0ehi4]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h517, hlam, p557_1]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h520, hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [hc03, hlam, hphi, p557_1, u0ehi3]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h524, hlam, p557_1]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h518, hlam, p557_1]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h521, hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h523, hlam, p557_1]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h546, hlam, p557_1]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h519, hlam, p557_1]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h522, hlam, p557_0]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [hc05, hlam, hphi, p557_1, u0ehi2]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [h519, hc01, hlam, hphi, p557_1, u0ehi3]
                                · have p557_0 := h557c.1
                                  have p557_1 := h557c.2.1
                                  have p557_2 := h557c.2.2.1
                                  have p557_3 := h557c.2.2.2
                                  linarith only [hlam, p557_0]
                        · linarith only [h0, h550, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h0, h517, h548, h549, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h519, h548, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h586 | h586
                · rcases m.htr 0 4 5 (by decide) (by decide) with h587 | h587
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h590 | h590
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h591 | h591
                          · linarith only [h0, h518, h591, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h518, h587, h589, h591, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h519, h590, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h517, h588, h589, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h519, h588, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h523, h586, h587, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h598 | h598
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h599 | h599
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h601 | h601
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h602 | h602
                          · linarith only [h0, h518, h602, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h518, h598, h600, h602, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h519, h601, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h0, h517, h599, h600, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h599, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h608 | h608
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h609 | h609
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h610 | h610
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h611 | h611
                          · linarith only [h0, h518, h523, h598, h611, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h613 | h613
                            · linarith only [h0, h517, h586, h608, h613, hc12, hlam, hphi, ht01, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h615 | h615
                              · linarith only [h0, h519, h523, h598, h609, h611, h615, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases h0bigk with h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h523, hc12, hlam, hphi, ht01, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h523, h598, hc12, hlam, hphi, ht01, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h519, hc12, hlam, hphi, ht01, ht0b, ht5b, p617_1, u5ehi1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h523, hc12, hlam, hphi, ht01, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h523, h598, hc12, hlam, hphi, ht01, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h517, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h520, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h523, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h586, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h518, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h521, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hc04, hlam, hphi, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h598, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h519, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h522, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h519, hc01, hlam, hphi, p617_1, u0ehi2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h519, hc12, hlam, hphi, ht01, p617_1, u0ehi3]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                        · linarith only [h0, h610, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h0, h517, h608, h609, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h608, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h520, h522, hc25, hlam, hphi, u2ehi2]
          · linarith only [h520, h521, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h517, h520, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h649 | h649
        · rcases m.htr 0 2 4 (by decide) (by decide) with h650 | h650
          · rcases m.htr 0 2 5 (by decide) (by decide) with h651 | h651
            · rcases m.htr 0 3 4 (by decide) (by decide) with h652 | h652
              · rcases m.htr 0 3 5 (by decide) (by decide) with h653 | h653
                · linarith only [h517, h519, h653, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
                  · linarith only [h517, h519, h652, h655, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h659 | h659
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h660 | h660
                          · linarith only [h518, h519, h655, h659, h660, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h518, h519, h658, h660, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                        · linarith only [h0, h518, h651, h658, h659, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h651, h658, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h657, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h666 | h666
                · linarith only [h518, h519, h652, h666, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h668 | h668
                  · linarith only [h518, h519, h668, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h671 | h671
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h672 | h672
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h673 | h673
                          · linarith only [h518, h652, h668, h673, hc01, hlam, hphi, u0ehi2]
                          · linarith only [h517, h519, h670, h673, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h517, h670, h672, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h517, h670, h671, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h670, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h649, h651, hc25, hlam, hphi, u2ehi2]
          · linarith only [h649, h650, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h517, h649, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h682 | h682
      · rcases m.htr 0 2 3 (by decide) (by decide) with h683 | h683
        · rcases m.htr 0 2 4 (by decide) (by decide) with h684 | h684
          · rcases m.htr 0 2 5 (by decide) (by decide) with h685 | h685
            · rcases m.htr 0 3 4 (by decide) (by decide) with h686 | h686
              · linarith only [h517, h518, h686, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h688 | h688
                · rcases m.htr 0 4 5 (by decide) (by decide) with h689 | h689
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h690 | h690
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h691 | h691
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h692 | h692
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h693 | h693
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h694 | h694
                            · linarith only [h517, h518, h690, h694, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h517, h518, h688, h691, h694, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h518, h682, h684, h689, h692, h693, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · linarith only [h0, h517, h690, h692, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h517, h690, h691, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h690, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h517, h518, h688, h689, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h702 | h702
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h703 | h703
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h704 | h704
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h705 | h705
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h706 | h706
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h707 | h707
                            · linarith only [h517, h688, h703, h707, hc01, hlam, hphi, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h709 | h709
                              · rcases h0bigk with h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h0, hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h518, h704, hc12, hlam, hphi, ht01, p710_1, u0ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h518, hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h518, h688, h704, hc12, hlam, hphi, ht01, p710_1, u0ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h0, h682, hc12, hlam, hphi, ht01, ht0b, ht5b, p710_1, u5ehi1]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p710_1, u0ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p710_1, u0ehi3]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h0, h688, hc12, hlam, hphi, ht01, p710_1, u0ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h517, hlam, p710_1]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h683, hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h686, hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h688, hlam, p710_1]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h682, h705, h707, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p710_1, u2ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h684, hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h686, hc34, hlam, hphi, ht01, ht12, ht23, p710_1, u0ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h518, h682, h686, h688, h704, h705, h707, hc12, hc34, hlam, hphi, ht01, ht23, p710_1, u0ehi2, u2ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h682, hlam, p710_1]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h685, hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [hc05, hlam, hphi, p710_1, u0ehi2]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [h702, hlam, p710_0]
                                · have p710_0 := h710c.1
                                  have p710_1 := h710c.2.1
                                  have p710_2 := h710c.2.2.1
                                  have p710_3 := h710c.2.2.2
                                  linarith only [hlam, p710_0]
                              · linarith only [h686, h702, h709, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h518, h686, h702, h706, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h517, h518, h703, h704, h705, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h517, h703, h704, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h682, h703, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h518, h682, h702, hlam]
            · linarith only [h684, h685, hc25, hlam, hphi, u2ehi3]
          · linarith only [h683, h684, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h517, h683, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h745 | h745
        · rcases m.htr 0 2 4 (by decide) (by decide) with h746 | h746
          · rcases m.htr 0 2 5 (by decide) (by decide) with h747 | h747
            · rcases m.htr 0 3 4 (by decide) (by decide) with h748 | h748
              · linarith only [h517, h518, h748, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h750 | h750
                · linarith only [h517, h682, h750, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h752 | h752
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h754 | h754
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h755 | h755
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h756 | h756
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h757 | h757
                            · linarith only [h517, h682, h750, h753, h754, h756, h757, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h759 | h759
                              · rcases h0bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h0, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h682, h754, h756, hc12, hlam, hphi, ht01, p760_1, u0ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h518, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h682, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h0, h517, h753, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p760_1, u2ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p760_1, u0ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h0, h517, h682, h752, h753, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p760_1, u2ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h0, h517, h682, h753, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p760_1, u2ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h517, hlam, p760_1]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h745, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h748, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h750, hlam, p760_1]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h517, h753, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1, u2ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h746, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h748, hc34, hlam, hphi, ht01, ht12, ht23, p760_1, u0ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h517, h682, h748, h753, hc34, hlam, hphi, ht23, p760_1, u2ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h517, h753, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1, u2ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h747, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h517, h682, h750, h753, h754, h756, hc12, hc35, hlam, hphi, ht01, ht23, p760_1, u0ehi2, u2ehi2]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [h752, hlam, p760_0]
                                · have p760_0 := h760c.1
                                  have p760_1 := h760c.2.1
                                  have p760_2 := h760c.2.2.1
                                  have p760_3 := h760c.2.2.2
                                  linarith only [hlam, p760_0]
                              · linarith only [h748, h752, h759, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h517, h518, h748, h752, h753, h756, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h0, h747, h755, hlam]
                      · linarith only [h0, h747, h754, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h753, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
                    · linarith only [h517, h518, h752, h791, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h791, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h745, h747, hc25, hlam, hphi, u2ehi2]
          · linarith only [h745, h746, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h517, h745, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h797 | h797
    · rcases m.htr 0 1 5 (by decide) (by decide) with h798 | h798
      · rcases m.htr 0 2 3 (by decide) (by decide) with h799 | h799
        · rcases m.htr 0 2 4 (by decide) (by decide) with h800 | h800
          · rcases m.htr 0 2 5 (by decide) (by decide) with h801 | h801
            · rcases m.htr 0 3 4 (by decide) (by decide) with h802 | h802
              · rcases m.htr 0 3 5 (by decide) (by decide) with h803 | h803
                · rcases m.htr 0 4 5 (by decide) (by decide) with h804 | h804
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h806 | h806
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h807 | h807
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h808 | h808
                          · linarith only [h517, h797, h808, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h517, h797, h804, h805, h806, h808, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h517, h798, h805, h807, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h517, h798, h805, h806, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h797, h804, h805, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h814 | h814
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h815 | h815
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h816 | h816
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h817 | h817
                          · linarith only [h517, h797, h804, h814, h817, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h819 | h819
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h820 | h820
                              · linarith only [h517, h798, h804, h814, h815, h817, h820, hc12, hlam, hphi, ht01, u0ehi3]
                              · rcases h0bigk with h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h0, hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h517, hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, p822_1, u0ehi3]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, ht0b, ht5b, p822_1, u5ehi0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h0, h798, h815, h817, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p822_1, u2ehi3]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p822_1, u0ehi2]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p822_1, u0ehi3]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p822_1, u0ehi4]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h798, h815, h817, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p822_1, u2ehi3]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h799, hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, p822_1, u0ehi3]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, p822_1, u0ehi4]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h797, hlam, p822_1]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h800, hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h802, hlam, p822_1]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h804, hlam, p822_1]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h798, hlam, p822_1]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h801, hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [h803, hlam, p822_0]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [hc05, hlam, hphi, p822_1, u0ehi3]
                                · have p822_0 := h822c.1
                                  have p822_1 := h822c.2.1
                                  have p822_2 := h822c.2.2.1
                                  have p822_3 := h822c.2.2.2
                                  linarith only [hlam, p822_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                              · linarith only [h798, h804, h815, h817, h848, hc01, hlam, hphi, u0ehi3]
                              · rcases h0bigk with h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h0, hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h517, hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, p850_1, u0ehi3]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, ht0b, ht5b, p850_1, u5ehi0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h0, h798, hc12, hlam, hphi, ht01, ht0b, ht5b, p850_1, u5ehi1]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p850_1, u0ehi2]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p850_1, u0ehi3]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p850_1, u0ehi4]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h798, h815, h817, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p850_1, u2ehi3]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h799, hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, p850_1, u0ehi3]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h517, h814, hc12, hlam, hphi, ht01, p850_1, u0ehi4]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h797, hlam, p850_1]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h800, hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h802, hlam, p850_1]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h804, hlam, p850_1]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h798, hlam, p850_1]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h801, hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [h803, hlam, p850_0]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [hc05, hlam, hphi, p850_1, u0ehi3]
                                · have p850_0 := h850c.1
                                  have p850_1 := h850c.2.1
                                  have p850_2 := h850c.2.2.1
                                  have p850_3 := h850c.2.2.2
                                  linarith only [hlam, p850_0]
                        · linarith only [h0, h798, h816, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h517, h798, h804, h814, h815, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                    · linarith only [h0, h798, h804, h814, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h517, h798, h803, hlam]
              · linarith only [h517, h797, h802, hlam]
            · linarith only [h799, h801, hc25, hlam, hphi, u2ehi2]
          · linarith only [h799, h800, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h883 | h883
          · linarith only [h799, h883, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h797, h883, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h886 | h886
        · rcases m.htr 0 2 4 (by decide) (by decide) with h887 | h887
          · rcases m.htr 0 2 5 (by decide) (by decide) with h888 | h888
            · rcases m.htr 0 3 4 (by decide) (by decide) with h889 | h889
              · rcases m.htr 0 3 5 (by decide) (by decide) with h890 | h890
                · rcases m.htr 0 4 5 (by decide) (by decide) with h891 | h891
                  · linarith only [h797, h798, h891, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h893 | h893
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h894 | h894
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h895 | h895
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h896 | h896
                          · linarith only [h517, h797, h891, h896, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h797, h798, h894, h896, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                        · linarith only [h517, h797, h888, h893, h894, h895, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h797, h894, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                    · linarith only [h0, h797, h886, h893, hc02, hlam, hphi, u0ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
                  · linarith only [h517, h797, h890, h902, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h904 | h904
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h905 | h905
                      · linarith only [h517, h797, h890, h905, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h905, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h886, h904, hlam]
              · linarith only [h517, h797, h889, hlam]
            · linarith only [h886, h888, hc25, hlam, hphi, u2ehi2]
          · linarith only [h886, h887, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h912 | h912
          · linarith only [h886, h912, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h797, h912, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h915 | h915
      · rcases m.htr 0 2 3 (by decide) (by decide) with h916 | h916
        · rcases m.htr 0 2 4 (by decide) (by decide) with h917 | h917
          · rcases m.htr 0 2 5 (by decide) (by decide) with h918 | h918
            · rcases m.htr 0 3 4 (by decide) (by decide) with h919 | h919
              · rcases m.htr 0 3 5 (by decide) (by decide) with h920 | h920
                · rcases m.htr 0 4 5 (by decide) (by decide) with h921 | h921
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h924 | h924
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h925 | h925
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h926 | h926
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h927 | h927
                              · rcases h0bigk with h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h0, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h517, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h797, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h797, hc14, hlam, hphi, ht01, ht0b, ht5b, p928_1, u5ehi0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hc02, hlam, hphi, p928_1, u0ehi0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h0, h797, h915, h919, h924, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h0, h797, h915, h924, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p928_1, u0ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h915, h924, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h916, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h517, h797, h915, h922, h924, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h517, h922, hc12, hlam, hphi, ht01, p928_1, u0ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h915, h924, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h917, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h919, hlam, p928_1]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h517, h919, h922, hc12, hlam, hphi, ht01, p928_1, u0ehi4]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h915, hlam, p928_1]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h918, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h920, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [h921, hlam, p928_0]
                                · have p928_0 := h928c.1
                                  have p928_1 := h928c.2.1
                                  have p928_2 := h928c.2.2.1
                                  have p928_3 := h928c.2.2.2
                                  linarith only [hlam, p928_0]
                              · linarith only [h0, h915, h925, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h955 | h955
                              · rcases h0bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h517, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h797, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h517, h922, hc12, hlam, hphi, ht01, ht0b, ht5b, p956_1, u5ehi0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, h915, hc12, hlam, hphi, ht01, ht0b, ht5b, p956_1, u5ehi1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p956_1, u0ehi2]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, h797, h915, hc12, hlam, hphi, ht01, ht0b, ht5b, p956_1, u5ehi1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p956_1, u0ehi4]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h915, hc03, hlam, hphi, ht0b, ht5b, p956_1, u5ehi1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h916, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h517, h797, h915, h922, hc12, hlam, hphi, ht01, ht0b, ht5b, p956_1, u5ehi1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h517, h922, hc12, hlam, hphi, ht01, p956_1, u0ehi4]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h915, hc04, hlam, hphi, ht0b, ht5b, p956_1, u5ehi1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h917, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h919, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h517, h919, h922, hc12, hlam, hphi, ht01, p956_1, u0ehi4]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h915, hlam, p956_1]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h918, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h920, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [h921, hlam, p956_0]
                                · have p956_0 := h956c.1
                                  have p956_1 := h956c.2.1
                                  have p956_2 := h956c.2.2.1
                                  have p956_3 := h956c.2.2.2
                                  linarith only [hlam, p956_0]
                              · linarith only [h0, h915, h925, h955, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h797, h915, h925, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                        · linarith only [h0, h915, h924, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h517, h915, h922, h923, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h917, h922, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h797, h915, h921, hlam]
                · linarith only [h517, h915, h920, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h989 | h989
                · rcases m.htr 0 4 5 (by decide) (by decide) with h990 | h990
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h991 | h991
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h992 | h992
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h993 | h993
                        · linarith only [h517, h915, h919, h993, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h517, h915, h991, h993, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                      · linarith only [h517, h915, h917, h991, h992, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · linarith only [h0, h915, h991, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h517, h915, h919, h990, hlam]
                · linarith only [h517, h915, h989, hlam]
            · linarith only [h916, h918, hc25, hlam, hphi, u2ehi2]
          · linarith only [h916, h917, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1002 | h1002
          · linarith only [h1002, h916, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1004 | h1004
            · linarith only [h1004, h916, hc23, hlam, hphi, u2ehi4]
            · linarith only [h0, h1004, h915, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1007 | h1007
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1008 | h1008
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1009 | h1009
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1010 | h1010
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1011 | h1011
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1012 | h1012
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1013 | h1013
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1014 | h1014
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1015 | h1015
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1016 | h1016
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1017 | h1017
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1018 | h1018
                              · rcases h0bigk with h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h0, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h517, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h797, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h915, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1019_1, u0ehi2]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h0, h1012, h915, hc12, hlam, hphi, ht01, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h0, h915, hc12, hlam, hphi, ht01, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hc03, hlam, hphi, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h1007, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h0, h1007, h1008, h1018, hc12, hlam, hphi, ht01, ht0b, ht5b, p1019_1, u5ehi4]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h0, h1007, h915, hc12, hlam, hphi, ht01, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hc04, hlam, hphi, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h1008, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h1010, hlam, p1019_1]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h0, h1007, h1010, h915, hc12, hlam, hphi, ht01, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hc05, hlam, hphi, p1019_1, u0ehi0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h1009, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h1011, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [h1012, hlam, p1019_0]
                                · have p1019_0 := h1019c.1
                                  have p1019_1 := h1019c.2.1
                                  have p1019_2 := h1019c.2.2.1
                                  have p1019_3 := h1019c.2.2.2
                                  linarith only [hlam, p1019_0]
                              · rcases h0bigk with h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h0, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h517, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h797, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h915, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1045_1, u0ehi0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h0, h1010, h1012, h1018, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1045_1, u2ehi3]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h0, h1012, h1018, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1045_1, u2ehi3]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1045_1, u0ehi4]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hc03, hlam, hphi, p1045_1, u0ehi0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1007, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1012, h1013, h1018, h517, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1045_1, u2ehi3]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1013, h517, h915, hc12, hlam, hphi, ht01, p1045_1, u0ehi0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hc04, hlam, hphi, p1045_1, u0ehi0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1008, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1010, hlam, p1045_1]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1010, h1013, h517, h915, hc12, hlam, hphi, ht01, p1045_1, u0ehi0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hc05, hlam, hphi, p1045_1, u0ehi0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1009, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1011, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [h1012, hlam, p1045_0]
                                · have p1045_0 := h1045c.1
                                  have p1045_1 := h1045c.2.1
                                  have p1045_2 := h1045c.2.2.1
                                  have p1045_3 := h1045c.2.2.2
                                  linarith only [hlam, p1045_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1071 | h1071
                              · rcases h0bigk with h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c | h1072c
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h0, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h517, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h797, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h915, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1072_1, u0ehi0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h0, h1011, h1017, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1072_1]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1072_1, u0ehi3]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h0, h915, hc12, hlam, hphi, ht01, p1072_1, u0ehi0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hc03, hlam, hphi, p1072_1, u0ehi0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1007, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1012, h1013, h517, h915, hc12, hlam, hphi, ht01, p1072_1, u0ehi0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1013, h517, h915, hc12, hlam, hphi, ht01, p1072_1, u0ehi0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hc04, hlam, hphi, p1072_1, u0ehi0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1008, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1010, hlam, p1072_1]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1010, h1011, h1013, h1017, h517, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1072_1, u2ehi2]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hc05, hlam, hphi, p1072_1, u0ehi0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1009, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1011, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [h1012, hlam, p1072_0]
                                · have p1072_0 := h1072c.1
                                  have p1072_1 := h1072c.2.1
                                  have p1072_2 := h1072c.2.2.1
                                  have p1072_3 := h1072c.2.2.2
                                  linarith only [hlam, p1072_0]
                              · rcases h0bigk with h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c | h1098c
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h0, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h517, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h797, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h915, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1098_1, u0ehi0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h0, h1010, h1012, h1071, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1098_1]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h0, h1012, h1071, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1098_1, u2ehi3]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1098_1, u0ehi4]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hc03, hlam, hphi, p1098_1, u0ehi0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1007, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1012, h1013, h1071, h517, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1098_1, u2ehi3]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1013, h517, h915, hc12, hlam, hphi, ht01, p1098_1, u0ehi0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hc04, hlam, hphi, p1098_1, u0ehi0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1008, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1010, hlam, p1098_1]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1010, h1011, h1013, h1017, h517, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1098_1, u2ehi2]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hc05, hlam, hphi, p1098_1, u0ehi0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1009, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1011, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [h1012, hlam, p1098_0]
                                · have p1098_0 := h1098c.1
                                  have p1098_1 := h1098c.2.1
                                  have p1098_2 := h1098c.2.2.1
                                  have p1098_3 := h1098c.2.2.2
                                  linarith only [hlam, p1098_0]
                          · linarith only [h1016, h797, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                        · linarith only [h0, h1015, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h0, h1009, h1014, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1008, h1013, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1128 | h1128
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1129 | h1129
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1130 | h1130
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1131 | h1131
                          · linarith only [h1012, h1131, hc14, hlam, hphi, ht01, u0ehi3]
                          · linarith only [h1131, h797, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                        · linarith only [h1009, h1128, h1130, h517, hc02, hlam, hphi, u0ehi0]
                      · linarith only [h0, h1129, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h1007, h1128, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1137 | h1137
                  · linarith only [h1010, h1011, h1137, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1139 | h1139
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1140 | h1140
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1141 | h1141
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1142 | h1142
                          · linarith only [h1137, h1142, hc14, hlam, hphi, ht01, u0ehi3]
                          · linarith only [h1142, h797, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                        · linarith only [h0, h1009, h1141, hlam]
                      · linarith only [h0, h1008, h1140, hlam]
                    · linarith only [h0, h1007, h1139, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1148 | h1148
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1149 | h1149
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1150 | h1150
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1151 | h1151
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1152 | h1152
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1153 | h1153
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1154 | h1154
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1155 | h1155
                              · rcases h0bigk with h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h517, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h797, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h915, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1156_1, u0ehi0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1156_1, u0ehi2]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, h1007, h1010, h1154, hc12, hlam, hphi, ht01, ht0b, ht5b, p1156_1, u5ehi3]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h0, h915, hc12, hlam, hphi, ht01, p1156_1, u0ehi0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hc03, hlam, hphi, p1156_1, u0ehi0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1007, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1010, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1010, h915, hc34, hlam, hphi, ht01, ht12, ht23, p1156_1, u0ehi0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hc04, hlam, hphi, p1156_1, u0ehi0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1008, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1010, hc34, hlam, hphi, ht01, ht12, ht23, p1156_1, u0ehi2]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1010, h915, hc34, hlam, hphi, ht01, ht12, ht23, p1156_1, u0ehi0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hc05, hlam, hphi, p1156_1, u0ehi0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1009, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1148, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [h1149, hlam, p1156_0]
                                · have p1156_0 := h1156c.1
                                  have p1156_1 := h1156c.2.1
                                  have p1156_2 := h1156c.2.2.1
                                  have p1156_3 := h1156c.2.2.2
                                  linarith only [hlam, p1156_0]
                              · linarith only [h1010, h1149, h1155, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h1010, h1148, h1154, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h1010, h1148, h1149, h1153, h797, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                        · linarith only [h0, h1152, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h0, h1151, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h1007, h1150, hc02, hlam, hphi, u0ehi0]
                  · linarith only [h1010, h1148, h1149, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1189 | h1189
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1190 | h1190
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1191 | h1191
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1192 | h1192
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1193 | h1193
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1194 | h1194
                            · linarith only [h1007, h1148, h1194, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1196 | h1196
                              · rcases h0bigk with h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h0, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h517, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h797, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h915, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1197_1, u0ehi0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1197_1, u0ehi2]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h0, h1008, h1196, hc12, hlam, hphi, ht01, ht0b, ht5b, p1197_1, u5ehi4]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht01, p1197_1, u0ehi4]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hc03, hlam, hphi, p1197_1, u0ehi0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1007, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1010, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1148, hlam, p1197_1]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hc04, hlam, hphi, p1197_1, u0ehi0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1008, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1010, hc34, hlam, hphi, ht01, ht12, ht23, p1197_1, u0ehi2]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1010, h1148, h517, hc34, hlam, hphi, ht01, ht12, ht23, p1197_1, u0ehi0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hc05, hlam, hphi, p1197_1, u0ehi0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1009, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1191, h1193, h517, h915, hc12, hlam, hphi, ht01, p1197_1, u0ehi0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [h1189, hlam, p1197_0]
                                · have p1197_0 := h1197c.1
                                  have p1197_1 := h1197c.2.1
                                  have p1197_2 := h1197c.2.2.1
                                  have p1197_3 := h1197c.2.2.2
                                  linarith only [hlam, p1197_0]
                              · linarith only [h1010, h1189, h1196, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1010, h1189, h1193, h797, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                        · linarith only [h0, h1009, h1192, hlam]
                      · linarith only [h0, h1009, h1191, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1008, h1190, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1231 | h1231
                          · linarith only [h1010, h1189, h1231, hc14, hlam, hphi, ht01, u0ehi2]
                          · linarith only [h1231, h797, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                        · linarith only [h1228, h1230, h517, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                      · linarith only [h1008, h1228, h1229, h517, hc02, hlam, hphi, u0ehi0]
                    · linarith only [h0, h1228, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h1007, h1009, hc25, hlam, hphi, u2ehi2]
          · linarith only [h1007, h1008, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1239 | h1239
          · linarith only [h1007, h1239, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1241 | h1241
            · linarith only [h1007, h1241, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1243 | h1243
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1244 | h1244
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1245 | h1245
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1246 | h1246
                    · linarith only [h1007, h1246, hc12, hlam, hphi, ht01, u0ehi1]
                    · linarith only [h0, h1246, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1249 | h1249
                    · linarith only [h0, h1007, h1249, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h1249, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1252 | h1252
                  · linarith only [h1243, h1244, h1252, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1254 | h1254
                    · linarith only [h0, h1007, h1254, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h1254, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1257 | h1257
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1258 | h1258
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1259 | h1259
                    · linarith only [h0, h1007, h1259, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h1259, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h1243, h1257, h1258, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1263 | h1263
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1264 | h1264
                    · linarith only [h0, h1007, h1264, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h1264, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1267 | h1267
                    · linarith only [h0, h1007, h1267, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h1267, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem r1l7_20_12_13_15_M_IR_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_IR_L_R_L_I_L_R_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_IR_L_R_L_I_L_R_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
