import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5139 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5140 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5141 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h5505 | h5505
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5506 | h5506
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5507 | h5507
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5508 | h5508
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5509 | h5509
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5510 | h5510
            · linarith only [h0, h5135, h5141, h5510, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5512 | h5512
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5513 | h5513
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5514 | h5514
                  · linarith only [h5135, h5141, h5507, h5514, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5516 | h5516
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5517 | h5517
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5518 | h5518
                        · rcases h2bigk with h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h0, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h0, h5516, h5518, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h0, h5514, h5516, h5518, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            rcases p5519_3 (m.d 0 2) (by simp) with h5524 | h5524
                            · rcases p5519_3 (m.d 1 2) (by simp) with h5525 | h5525
                              · rcases p5519_3 (m.d 2 3) (by simp) with h5526 | h5526
                                · linarith only [h5138, h5526, hlam]
                                · linarith only [h5516, h5526, hlam]
                              · linarith only [h5509, h5525, hlam]
                            · linarith only [h5524, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5516, h5518, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5514, h5516, h5518, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            rcases p5519_3 (m.d 0 2) (by simp) with h5535 | h5535
                            · linarith only [h0, h5535, hlam]
                            · linarith only [h5140, h5535, hlam]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5138, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5507, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5514, hlam, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5136, h5508, h5514, h5516, h5518, hc01, hc45, hlam, hphi, ht0b, ht5b, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5139, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5508, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h0, h5136, h5508, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h0, h5136, h5508, h5516, h5518, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5140, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5509, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5516, hlam, p5519_0]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [h5517, hlam, p5519_1]
                          · have p5519_0 := h5519c.1
                            have p5519_1 := h5519c.2.1
                            have p5519_2 := h5519c.2.2.1
                            have p5519_3 := h5519c.2.2.2
                            linarith only [hlam, p5519_0]
                        · linarith only [h5135, h5141, h5506, h5507, h5516, h5518, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h5136, h5513, h5517, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h5141, h5505, h5516, hc23, hc34, hlam, hphi]
                · linarith only [h0, h5136, h5506, h5510, h5512, h5513, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h5141, h5505, h5507, h5512, hc23, hc34, hlam, hphi]
          · linarith only [h0, h5140, h5509, hlam]
        · linarith only [h0, h5139, h5508, hlam]
      · linarith only [h0, h5138, h5507, hlam]
    · linarith only [h5141, h5505, h5506, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5562 | h5562
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5563 | h5563
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5564 | h5564
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5565 | h5565
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5566 | h5566
            · linarith only [h0, h5135, h5141, h5566, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5568 | h5568
              · linarith only [h5135, h5505, h5568, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5570 | h5570
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5571 | h5571
                  · linarith only [h0, h5135, h5141, h5563, h5571, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5573 | h5573
                    · linarith only [h5135, h5505, h5563, h5573, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5575 | h5575
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5576 | h5576
                        · rcases h2bigk with h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h0, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            rcases p5577_3 (m.d 0 2) (by simp) with h5580 | h5580
                            · rcases p5577_3 (m.d 1 2) (by simp) with h5581 | h5581
                              · rcases p5577_3 (m.d 2 3) (by simp) with h5582 | h5582
                                · linarith only [h5582, hlam, p5577_0]
                                · rcases p5577_3 (m.d 2 4) (by simp) with h5584 | h5584
                                  · linarith only [h5139, h5584, hlam]
                                  · linarith only [h5571, h5584, hlam]
                              · linarith only [h5563, h5581, hlam]
                            · linarith only [h5580, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h0, h5575, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            rcases p5577_3 (m.d 0 2) (by simp) with h5590 | h5590
                            · rcases p5577_3 (m.d 1 2) (by simp) with h5591 | h5591
                              · rcases p5577_3 (m.d 2 3) (by simp) with h5592 | h5592
                                · linarith only [h5138, h5592, hlam]
                                · rcases p5577_3 (m.d 2 4) (by simp) with h5594 | h5594
                                  · linarith only [h5139, h5594, hlam]
                                  · linarith only [h5575, h5594, hlam]
                              · linarith only [h5565, h5591, hlam]
                            · linarith only [h5590, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            rcases p5577_3 (m.d 0 2) (by simp) with h5601 | h5601
                            · linarith only [h0, h5601, hlam]
                            · linarith only [h5138, h5601, hlam]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5575, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            rcases p5577_3 (m.d 0 2) (by simp) with h5605 | h5605
                            · linarith only [h0, h5605, hlam]
                            · linarith only [h5140, h5605, hlam]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5138, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5563, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5571, hlam, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5573, hlam, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5139, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5564, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5136, h5564, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5136, h5141, h5564, h5573, hc23, hc34, hlam, hphi, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5140, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5565, hlam, p5577_0]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h0, h5140, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [h5575, hlam, p5577_1]
                          · have p5577_0 := h5577c.1
                            have p5577_1 := h5577c.2.1
                            have p5577_2 := h5577c.2.2.1
                            have p5577_3 := h5577c.2.2.2
                            linarith only [hlam, p5577_0]
                        · linarith only [h5141, h5562, h5576, hlam]
                      · linarith only [h0, h5136, h5570, h5575, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5625 | h5625
                  · linarith only [h5141, h5562, h5563, h5566, h5570, h5625, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5627 | h5627
                    · linarith only [h5505, h5562, h5563, h5566, h5570, h5627, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5629 | h5629
                      · linarith only [h5564, h5570, h5629, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5631 | h5631
                        · rcases h2bigk with h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c | h5632c
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h0, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            rcases p5632_3 (m.d 0 2) (by simp) with h5635 | h5635
                            · rcases p5632_3 (m.d 1 2) (by simp) with h5636 | h5636
                              · rcases p5632_3 (m.d 2 3) (by simp) with h5637 | h5637
                                · linarith only [h5637, hlam, p5632_0]
                                · rcases p5632_3 (m.d 2 4) (by simp) with h5639 | h5639
                                  · linarith only [h5139, h5639, hlam]
                                  · linarith only [h5625, h5639, hlam]
                              · linarith only [h5563, h5636, hlam]
                            · linarith only [h5635, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            rcases p5632_3 (m.d 0 2) (by simp) with h5644 | h5644
                            · rcases p5632_3 (m.d 1 2) (by simp) with h5645 | h5645
                              · rcases p5632_3 (m.d 2 3) (by simp) with h5646 | h5646
                                · linarith only [h5138, h5646, hlam]
                                · rcases p5632_3 (m.d 2 4) (by simp) with h5648 | h5648
                                  · linarith only [h5648, hlam, p5632_0]
                                  · rcases p5632_3 (m.d 2 5) (by simp) with h5650 | h5650
                                    · linarith only [h5140, h5650, hlam]
                                    · linarith only [h5629, h5650, hlam]
                              · linarith only [h5564, h5645, hlam]
                            · linarith only [h5644, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            rcases p5632_3 (m.d 0 2) (by simp) with h5655 | h5655
                            · rcases p5632_3 (m.d 1 2) (by simp) with h5656 | h5656
                              · rcases p5632_3 (m.d 2 3) (by simp) with h5657 | h5657
                                · linarith only [h5138, h5657, hlam]
                                · rcases p5632_3 (m.d 2 4) (by simp) with h5659 | h5659
                                  · linarith only [h5139, h5659, hlam]
                                  · rcases p5632_3 (m.d 2 5) (by simp) with h5661 | h5661
                                    · linarith only [h5661, hlam, p5632_0]
                                    · rcases h3bigk with h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c | h5663c
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5141, h5563, hc23, hc34, hlam, hphi, p5663_1]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5141, hc23, hc34, hlam, hphi, p5663_1]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5141, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5505, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5135, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h0, h5135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5663_1]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5566, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5568, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5138, hlam, p5663_1]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5563, hlam, p5663_1]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5625, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5627, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        rcases p5663_3 (m.d 0 3) (by simp) with h5679 | h5679
                                        · linarith only [h5679, hlam, p5663_0]
                                        · rcases p5663_3 (m.d 1 3) (by simp) with h5681 | h5681
                                          · linarith only [h5566, h5681, hlam]
                                          · rcases p5663_3 (m.d 2 3) (by simp) with h5683 | h5683
                                            · linarith only [h5625, h5683, hlam]
                                            · rcases p5663_3 (m.d 3 4) (by simp) with h5685 | h5685
                                              · rcases p5663_3 (m.d 3 5) (by simp) with h5686 | h5686
                                                · linarith only [h5631, h5686, hlam]
                                                · linarith only [h5505, h5686, hlam]
                                              · linarith only [h5685, hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        rcases p5663_3 (m.d 0 3) (by simp) with h5690 | h5690
                                        · linarith only [h5141, h5690, hlam]
                                        · linarith only [h5135, h5690, hlam]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        rcases p5663_3 (m.d 0 3) (by simp) with h5693 | h5693
                                        · linarith only [h5141, h5693, hlam]
                                        · linarith only [h5138, h5693, hlam]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [hlam, p5663_0]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5505, hc03, hc34, hlam, hphi, p5663_1]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        rcases p5663_3 (m.d 0 3) (by simp) with h5698 | h5698
                                        · linarith only [h5698, hlam, p5663_0]
                                        · rcases p5663_3 (m.d 1 3) (by simp) with h5700 | h5700
                                          · linarith only [h5568, h5700, hlam]
                                          · rcases p5663_3 (m.d 2 3) (by simp) with h5702 | h5702
                                            · linarith only [h5627, h5702, hlam]
                                            · rcases p5663_3 (m.d 3 4) (by simp) with h5704 | h5704
                                              · rcases p5663_3 (m.d 3 5) (by simp) with h5705 | h5705
                                                · rcases h5bigk with h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c | h5706c
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    rcases p5706_3 (m.d 0 5) (by simp) with h5708 | h5708
                                                    · rcases p5706_3 (m.d 1 5) (by simp) with h5709 | h5709
                                                      · linarith only [h5137, h5709, hlam]
                                                      · rcases p5706_3 (m.d 2 5) (by simp) with h5711 | h5711
                                                        · linarith only [h5140, h5711, hlam]
                                                        · rcases p5706_3 (m.d 3 5) (by simp) with h5713 | h5713
                                                          · rcases p5706_3 (m.d 4 5) (by simp) with h5714 | h5714
                                                            · linarith only [h5562, h5714, hlam]
                                                            · linarith only [h5570, h5714, hlam]
                                                          · linarith only [h5568, h5713, hlam]
                                                    · linarith only [h5137, h5708, hlam]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    rcases p5706_3 (m.d 0 5) (by simp) with h5719 | h5719
                                                    · rcases p5706_3 (m.d 1 5) (by simp) with h5720 | h5720
                                                      · linarith only [h5137, h5720, hlam]
                                                      · linarith only [h5565, h5720, hlam]
                                                    · linarith only [h5140, h5719, hlam]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5505, hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5505, h5563, h5566, h5570, hc23, hc35, hlam, hphi, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5137, hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h0, h5137, h5625, h5629, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5568, hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5570, hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5140, hlam, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5565, hlam, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5627, hlam, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5629, hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5562, h5563, h5566, h5570, hc23, hc35, hlam, hphi, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    rcases p5706_3 (m.d 0 5) (by simp) with h5737 | h5737
                                                    · linarith only [h5505, h5737, hlam]
                                                    · linarith only [h5137, h5737, hlam]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    rcases p5706_3 (m.d 0 5) (by simp) with h5740 | h5740
                                                    · linarith only [h5505, h5740, hlam]
                                                    · linarith only [h5140, h5740, hlam]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [hlam, p5706_0]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5563, h5566, h5570, h5631, hc23, hc34, hlam, hphi, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5562, hlam, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h0, h5136, h5562, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h0, h5136, h5562, h5625, h5629, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [h5631, hlam, p5706_1]
                                                  · have p5706_0 := h5706c.1
                                                    have p5706_1 := h5706c.2.1
                                                    have p5706_2 := h5706c.2.2.1
                                                    have p5706_3 := h5706c.2.2.2
                                                    linarith only [hlam, p5706_0]
                                                · linarith only [h5705, hlam, p5663_0]
                                              · linarith only [h5141, h5704, hlam]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        rcases p5663_3 (m.d 0 3) (by simp) with h5752 | h5752
                                        · linarith only [h5505, h5752, hlam]
                                        · linarith only [h5135, h5752, hlam]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        rcases p5663_3 (m.d 0 3) (by simp) with h5755 | h5755
                                        · linarith only [h5505, h5755, hlam]
                                        · linarith only [h5138, h5755, hlam]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [h5631, hlam, p5663_1]
                                      · have p5663_0 := h5663c.1
                                        have p5663_1 := h5663c.2.1
                                        have p5663_2 := h5663c.2.2.1
                                        have p5663_3 := h5663c.2.2.2
                                        linarith only [hlam, p5663_0]
                              · linarith only [h5565, h5656, hlam]
                            · linarith only [h5655, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5632_1]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            rcases p5632_3 (m.d 0 2) (by simp) with h5764 | h5764
                            · linarith only [h0, h5764, hlam]
                            · linarith only [h5138, h5764, hlam]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            rcases p5632_3 (m.d 0 2) (by simp) with h5767 | h5767
                            · linarith only [h0, h5767, hlam]
                            · linarith only [h5139, h5767, hlam]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            rcases p5632_3 (m.d 0 2) (by simp) with h5770 | h5770
                            · linarith only [h0, h5770, hlam]
                            · linarith only [h5140, h5770, hlam]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5138, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5563, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5625, hlam, p5632_1]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5627, hlam, p5632_1]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5139, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5564, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5137, h5565, h5629, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5632_1]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5629, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5140, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h5565, hlam, p5632_0]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h0, h5136, h5562, h5565, h5570, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5632_1]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [h0, h5136, h5562, h5565, h5570, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5632_1]
                          · have p5632_0 := h5632c.1
                            have p5632_1 := h5632c.2.1
                            have p5632_2 := h5632c.2.2.1
                            have p5632_3 := h5632c.2.2.2
                            linarith only [hlam, p5632_0]
                        · linarith only [h0, h5135, h5136, h5141, h5562, h5563, h5631, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h5140, h5565, hlam]
        · linarith only [h0, h5139, h5564, hlam]
      · linarith only [h0, h5138, h5563, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5792 | h5792
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5793 | h5793
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5794 | h5794
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5795 | h5795
            · linarith only [h0, h5135, h5141, h5795, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5797 | h5797
              · linarith only [h5135, h5505, h5797, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5799 | h5799
                · linarith only [h0, h5136, h5562, h5799, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5801 | h5801
                  · linarith only [h5135, h5141, h5792, h5801, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5803 | h5803
                    · linarith only [h5135, h5505, h5792, h5803, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5805 | h5805
                      · linarith only [h5139, h5562, h5805, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5807 | h5807
                        · rcases h2bigk with h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c | h5808c
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h0, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            rcases p5808_3 (m.d 0 2) (by simp) with h5811 | h5811
                            · rcases p5808_3 (m.d 1 2) (by simp) with h5812 | h5812
                              · rcases p5808_3 (m.d 2 3) (by simp) with h5813 | h5813
                                · linarith only [h5813, hlam, p5808_0]
                                · rcases p5808_3 (m.d 2 4) (by simp) with h5815 | h5815
                                  · linarith only [h5139, h5815, hlam]
                                  · linarith only [h5801, h5815, hlam]
                              · linarith only [h5792, h5812, hlam]
                            · linarith only [h5811, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            rcases p5808_3 (m.d 0 2) (by simp) with h5820 | h5820
                            · rcases p5808_3 (m.d 1 2) (by simp) with h5821 | h5821
                              · rcases p5808_3 (m.d 2 3) (by simp) with h5822 | h5822
                                · linarith only [h5138, h5822, hlam]
                                · rcases p5808_3 (m.d 2 4) (by simp) with h5824 | h5824
                                  · linarith only [h5824, hlam, p5808_0]
                                  · rcases p5808_3 (m.d 2 5) (by simp) with h5826 | h5826
                                    · linarith only [h5140, h5826, hlam]
                                    · linarith only [h5805, h5826, hlam]
                              · linarith only [h5793, h5821, hlam]
                            · linarith only [h5820, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            rcases p5808_3 (m.d 0 2) (by simp) with h5831 | h5831
                            · rcases p5808_3 (m.d 1 2) (by simp) with h5832 | h5832
                              · rcases p5808_3 (m.d 2 3) (by simp) with h5833 | h5833
                                · linarith only [h5138, h5833, hlam]
                                · rcases p5808_3 (m.d 2 4) (by simp) with h5835 | h5835
                                  · linarith only [h5139, h5835, hlam]
                                  · rcases p5808_3 (m.d 2 5) (by simp) with h5837 | h5837
                                    · linarith only [h5837, hlam, p5808_0]
                                    · rcases h3bigk with h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c | h5839c
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5141, h5792, hc23, hc34, hlam, hphi, p5839_1]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5141, hc23, hc34, hlam, hphi, p5839_1]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5141, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5505, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5135, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h0, h5135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5839_1]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5795, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5797, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5138, hlam, p5839_1]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5792, hlam, p5839_1]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5801, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5803, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        rcases p5839_3 (m.d 0 3) (by simp) with h5855 | h5855
                                        · linarith only [h5855, hlam, p5839_0]
                                        · rcases p5839_3 (m.d 1 3) (by simp) with h5857 | h5857
                                          · linarith only [h5795, h5857, hlam]
                                          · rcases p5839_3 (m.d 2 3) (by simp) with h5859 | h5859
                                            · linarith only [h5801, h5859, hlam]
                                            · rcases p5839_3 (m.d 3 4) (by simp) with h5861 | h5861
                                              · rcases p5839_3 (m.d 3 5) (by simp) with h5862 | h5862
                                                · linarith only [h5807, h5862, hlam]
                                                · linarith only [h5505, h5862, hlam]
                                              · linarith only [h5861, hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        rcases p5839_3 (m.d 0 3) (by simp) with h5866 | h5866
                                        · linarith only [h5141, h5866, hlam]
                                        · linarith only [h5135, h5866, hlam]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        rcases p5839_3 (m.d 0 3) (by simp) with h5869 | h5869
                                        · linarith only [h5141, h5869, hlam]
                                        · linarith only [h5138, h5869, hlam]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [hlam, p5839_0]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5141, h5562, h5807, hc03, hc34, hlam, hphi, p5839_1]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        rcases p5839_3 (m.d 0 3) (by simp) with h5874 | h5874
                                        · linarith only [h5874, hlam, p5839_0]
                                        · rcases p5839_3 (m.d 1 3) (by simp) with h5876 | h5876
                                          · linarith only [h5797, h5876, hlam]
                                          · rcases p5839_3 (m.d 2 3) (by simp) with h5878 | h5878
                                            · linarith only [h5803, h5878, hlam]
                                            · rcases p5839_3 (m.d 3 4) (by simp) with h5880 | h5880
                                              · rcases p5839_3 (m.d 3 5) (by simp) with h5881 | h5881
                                                · rcases h5bigk with h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c | h5882c
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5562, h5792, h5795, h5799, h5807, hc23, hc34, hlam, hphi, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5562, h5801, h5805, h5807, hc23, hc34, hlam, hphi, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5505, hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5562, hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5137, hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h0, h5137, h5801, h5805, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5797, hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5799, hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5140, hlam, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5794, hlam, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5803, hlam, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5805, hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    rcases p5882_3 (m.d 0 5) (by simp) with h5898 | h5898
                                                    · linarith only [h5505, h5898, hlam]
                                                    · rcases p5882_3 (m.d 1 5) (by simp) with h5900 | h5900
                                                      · linarith only [h5797, h5900, hlam]
                                                      · rcases p5882_3 (m.d 2 5) (by simp) with h5902 | h5902
                                                        · linarith only [h5803, h5902, hlam]
                                                        · rcases p5882_3 (m.d 3 5) (by simp) with h5904 | h5904
                                                          · rcases p5882_3 (m.d 4 5) (by simp) with h5905 | h5905
                                                            · linarith only [h5807, h5905, hlam]
                                                            · linarith only [h5562, h5905, hlam]
                                                          · linarith only [h5505, h5904, hlam]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    rcases p5882_3 (m.d 0 5) (by simp) with h5909 | h5909
                                                    · linarith only [h5505, h5909, hlam]
                                                    · linarith only [h5137, h5909, hlam]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    rcases p5882_3 (m.d 0 5) (by simp) with h5912 | h5912
                                                    · linarith only [h5505, h5912, hlam]
                                                    · linarith only [h5140, h5912, hlam]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [hlam, p5882_0]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5136, h5562, h5792, h5795, hc23, hc35, hlam, hphi, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5136, h5562, h5792, h5795, h5807, hc23, hc34, hlam, hphi, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5794, h5801, h5805, h5807, hc23, hc34, hlam, hphi, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5801, h5805, h5807, hc23, hc34, hlam, hphi, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [h5807, hlam, p5882_1]
                                                  · have p5882_0 := h5882c.1
                                                    have p5882_1 := h5882c.2.1
                                                    have p5882_2 := h5882c.2.2.1
                                                    have p5882_3 := h5882c.2.2.2
                                                    linarith only [hlam, p5882_0]
                                                · linarith only [h5881, hlam, p5839_0]
                                              · linarith only [h5141, h5880, hlam]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        rcases p5839_3 (m.d 0 3) (by simp) with h5924 | h5924
                                        · linarith only [h5505, h5924, hlam]
                                        · linarith only [h5135, h5924, hlam]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        rcases p5839_3 (m.d 0 3) (by simp) with h5927 | h5927
                                        · linarith only [h5505, h5927, hlam]
                                        · linarith only [h5138, h5927, hlam]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [h5807, hlam, p5839_1]
                                      · have p5839_0 := h5839c.1
                                        have p5839_1 := h5839c.2.1
                                        have p5839_2 := h5839c.2.2.1
                                        have p5839_3 := h5839c.2.2.2
                                        linarith only [hlam, p5839_0]
                              · linarith only [h5794, h5832, hlam]
                            · linarith only [h5831, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5808_1]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            rcases p5808_3 (m.d 0 2) (by simp) with h5936 | h5936
                            · linarith only [h0, h5936, hlam]
                            · linarith only [h5138, h5936, hlam]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            rcases p5808_3 (m.d 0 2) (by simp) with h5939 | h5939
                            · linarith only [h0, h5939, hlam]
                            · linarith only [h5139, h5939, hlam]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            rcases p5808_3 (m.d 0 2) (by simp) with h5942 | h5942
                            · linarith only [h0, h5942, hlam]
                            · linarith only [h5140, h5942, hlam]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5138, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5792, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5801, hlam, p5808_1]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5803, hlam, p5808_1]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5139, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5793, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5137, h5794, h5805, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5808_1]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5805, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5140, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h5794, hlam, p5808_0]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h0, h5137, h5794, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5808_1]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [h0, h5137, h5794, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5808_1]
                          · have p5808_0 := h5808c.1
                            have p5808_1 := h5808c.2.1
                            have p5808_2 := h5808c.2.2.1
                            have p5808_3 := h5808c.2.2.2
                            linarith only [hlam, p5808_0]
                        · rcases h2bigk with h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c | h5960c
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h0, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 2) (by simp) with h5963 | h5963
                            · rcases p5960_3 (m.d 1 2) (by simp) with h5964 | h5964
                              · rcases p5960_3 (m.d 2 3) (by simp) with h5965 | h5965
                                · linarith only [h5965, hlam, p5960_0]
                                · rcases p5960_3 (m.d 2 4) (by simp) with h5967 | h5967
                                  · linarith only [h5139, h5967, hlam]
                                  · linarith only [h5801, h5967, hlam]
                              · linarith only [h5792, h5964, hlam]
                            · linarith only [h5963, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 2) (by simp) with h5972 | h5972
                            · rcases p5960_3 (m.d 1 2) (by simp) with h5973 | h5973
                              · rcases p5960_3 (m.d 2 3) (by simp) with h5974 | h5974
                                · linarith only [h5138, h5974, hlam]
                                · rcases p5960_3 (m.d 2 4) (by simp) with h5976 | h5976
                                  · linarith only [h5976, hlam, p5960_0]
                                  · rcases p5960_3 (m.d 2 5) (by simp) with h5978 | h5978
                                    · linarith only [h5140, h5978, hlam]
                                    · linarith only [h5805, h5978, hlam]
                              · linarith only [h5793, h5973, hlam]
                            · linarith only [h5972, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 2) (by simp) with h5983 | h5983
                            · rcases p5960_3 (m.d 1 2) (by simp) with h5984 | h5984
                              · rcases p5960_3 (m.d 2 3) (by simp) with h5985 | h5985
                                · linarith only [h5138, h5985, hlam]
                                · rcases p5960_3 (m.d 2 4) (by simp) with h5987 | h5987
                                  · linarith only [h5139, h5987, hlam]
                                  · rcases p5960_3 (m.d 2 5) (by simp) with h5989 | h5989
                                    · linarith only [h5989, hlam, p5960_0]
                                    · rcases h3bigk with h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c | h5991c
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5141, h5792, h5807, hc23, hc45, hlam, hphi, ht34, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5141, h5807, hc23, hc45, hlam, hphi, ht34, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5141, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5505, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5135, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h0, h5135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5795, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5797, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5138, hlam, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5792, hlam, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5801, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5803, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5807, hc03, hc45, hlam, hphi, ht34, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5807, hc13, hc45, hlam, hphi, ht34, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5807, hc23, hc45, hlam, hphi, ht34, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5807, hlam, p5991_0]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        rcases p5991_3 (m.d 0 3) (by simp) with h6012 | h6012
                                        · linarith only [h6012, hlam, p5991_0]
                                        · rcases p5991_3 (m.d 1 3) (by simp) with h6014 | h6014
                                          · linarith only [h5797, h6014, hlam]
                                          · rcases p5991_3 (m.d 2 3) (by simp) with h6016 | h6016
                                            · linarith only [h5803, h6016, hlam]
                                            · rcases p5991_3 (m.d 3 4) (by simp) with h6018 | h6018
                                              · linarith only [h5807, h6018, hlam]
                                              · linarith only [h5141, h6018, hlam]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        rcases p5991_3 (m.d 0 3) (by simp) with h6021 | h6021
                                        · linarith only [h5505, h6021, hlam]
                                        · linarith only [h5135, h6021, hlam]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        rcases p5991_3 (m.d 0 3) (by simp) with h6024 | h6024
                                        · linarith only [h5505, h6024, hlam]
                                        · linarith only [h5138, h6024, hlam]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [h5141, h5807, hc03, hc45, hlam, hphi, ht34, p5991_1]
                                      · have p5991_0 := h5991c.1
                                        have p5991_1 := h5991c.2.1
                                        have p5991_2 := h5991c.2.2.1
                                        have p5991_3 := h5991c.2.2.2
                                        linarith only [hlam, p5991_0]
                              · linarith only [h5794, h5984, hlam]
                            · linarith only [h5983, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 2) (by simp) with h6033 | h6033
                            · linarith only [h0, h6033, hlam]
                            · linarith only [h5138, h6033, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 2) (by simp) with h6036 | h6036
                            · linarith only [h0, h6036, hlam]
                            · linarith only [h5139, h6036, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            rcases p5960_3 (m.d 0 2) (by simp) with h6039 | h6039
                            · linarith only [h0, h6039, hlam]
                            · linarith only [h5140, h6039, hlam]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5138, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5792, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5801, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5803, hlam, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5139, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5793, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5137, h5793, h5799, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5805, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5140, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h5794, hlam, p5960_0]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h0, h5140, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [h0, h5137, h5794, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5960_1]
                          · have p5960_0 := h5960c.1
                            have p5960_1 := h5960c.2.1
                            have p5960_2 := h5960c.2.2.1
                            have p5960_3 := h5960c.2.2.2
                            linarith only [hlam, p5960_0]
          · linarith only [h0, h5140, h5794, hlam]
        · linarith only [h0, h5139, h5793, hlam]
      · linarith only [h0, h5138, h5792, hlam]

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5139 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5140 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h5141 | h5141
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138 h5139 h5140 h5141
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138 h5139 h5140 h5141

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5139 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5140 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  linarith only [h0, h5137, h5140, hlam]

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5139 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h5140 | h5140
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138 h5139 h5140
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138 h5139 h5140

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5139 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  linarith only [h0, h5136, h5139, hlam]

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h5139 | h5139
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138 h5139
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138 h5139

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5138 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  linarith only [h0, h5135, h5138, hlam]

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h5138 | h5138
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 h5135 h5136 h5137 h5138

end R2N4
