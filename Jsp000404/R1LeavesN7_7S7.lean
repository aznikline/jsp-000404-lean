import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S5
import Jsp000404.R1LeavesN7_7S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10184000 in
set_option maxHeartbeats 10184000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3894 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h3981 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h4625 | h4625
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4626 | h4626
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4627 | h4627
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4628 | h4628
        · linarith only [h1, h4628, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4630 | h4630
          · linarith only [h1, h3894, h4630, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4632 | h4632
            · linarith only [h2, h3981, h4632, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4634 | h4634
              · linarith only [h1, h4625, h4634, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4636 | h4636
                · linarith only [h3894, h4, h4636, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4638 | h4638
                  · linarith only [h0, h3981, h4626, h4638, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4640 | h4640
                    · rcases h1bigk with h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c | h4641c
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h4627, hc01, hlam, hphi, ht0b, ht5b, p4641_1, u5ehi2]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        rcases p4641_3 (m.d 0 1) (by simp) with h4644 | h4644
                        · rcases p4641_3 (m.d 1 2) (by simp) with h4645 | h4645
                          · linarith only [h0, h4645, hlam]
                          · linarith only [h4625, h4645, hlam]
                        · linarith only [h4644, hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        rcases p4641_3 (m.d 0 1) (by simp) with h4649 | h4649
                        · rcases p4641_3 (m.d 1 2) (by simp) with h4650 | h4650
                          · linarith only [h0, h4650, hlam]
                          · linarith only [h4626, h4650, hlam]
                        · linarith only [h4649, hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        rcases p4641_3 (m.d 0 1) (by simp) with h4654 | h4654
                        · rcases p4641_3 (m.d 1 2) (by simp) with h4655 | h4655
                          · linarith only [h0, h4655, hlam]
                          · linarith only [h4627, h4655, hlam]
                        · linarith only [h4654, hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h0, hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        rcases p4641_3 (m.d 0 1) (by simp) with h4661 | h4661
                        · rcases p4641_3 (m.d 1 2) (by simp) with h4662 | h4662
                          · rcases p4641_3 (m.d 1 3) (by simp) with h4663 | h4663
                            · linarith only [h4625, h4663, hlam]
                            · rcases p4641_3 (m.d 1 4) (by simp) with h4665 | h4665
                              · linarith only [h4626, h4665, hlam]
                              · linarith only [h4628, h4665, hlam]
                          · linarith only [h4625, h4662, hlam]
                        · linarith only [h1, h4661, hlam]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        rcases p4641_3 (m.d 0 1) (by simp) with h4670 | h4670
                        · rcases p4641_3 (m.d 1 2) (by simp) with h4671 | h4671
                          · rcases p4641_3 (m.d 1 3) (by simp) with h4672 | h4672
                            · linarith only [h4625, h4672, hlam]
                            · rcases p4641_3 (m.d 1 4) (by simp) with h4674 | h4674
                              · linarith only [h4626, h4674, hlam]
                              · rcases p4641_3 (m.d 1 5) (by simp) with h4676 | h4676
                                · linarith only [h4627, h4676, hlam]
                                · linarith only [h4632, h4676, hlam]
                          · linarith only [h4626, h4671, hlam]
                        · linarith only [h2, h4670, hlam]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h0, h4627, hc01, hlam, hphi, ht0b, ht5b, p4641_1, u5ehi2]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h1, hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h4625, hlam, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h4628, hlam, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h4630, hlam, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h2, hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h4626, hlam, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h2, h3981, h4625, hc23, hc45, hlam, hphi, ht34, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h4632, hlam, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h3, hlam, p4641_0]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h4627, hlam, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h3, h3981, h4625, h4640, hc23, hc34, hlam, hphi, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [h3, h3981, h4625, h4628, h4640, hc23, hc34, hlam, hphi, p4641_1]
                      · have p4641_0 := h4641c.1
                        have p4641_1 := h4641c.2.1
                        have p4641_2 := h4641c.2.2.1
                        have p4641_3 := h4641c.2.2.2
                        linarith only [hlam, p4641_0]
                    · rcases h1bigk with h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h4627, hc01, hlam, hphi, ht0b, ht5b, p4697_1, u5ehi2]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        rcases p4697_3 (m.d 0 1) (by simp) with h4700 | h4700
                        · rcases p4697_3 (m.d 1 2) (by simp) with h4701 | h4701
                          · linarith only [h0, h4701, hlam]
                          · linarith only [h4625, h4701, hlam]
                        · linarith only [h4700, hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        rcases p4697_3 (m.d 0 1) (by simp) with h4705 | h4705
                        · rcases p4697_3 (m.d 1 2) (by simp) with h4706 | h4706
                          · linarith only [h0, h4706, hlam]
                          · linarith only [h4626, h4706, hlam]
                        · linarith only [h4705, hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        rcases p4697_3 (m.d 0 1) (by simp) with h4710 | h4710
                        · rcases p4697_3 (m.d 1 2) (by simp) with h4711 | h4711
                          · linarith only [h0, h4711, hlam]
                          · linarith only [h4627, h4711, hlam]
                        · linarith only [h4710, hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h0, hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        rcases p4697_3 (m.d 0 1) (by simp) with h4717 | h4717
                        · rcases p4697_3 (m.d 1 2) (by simp) with h4718 | h4718
                          · rcases p4697_3 (m.d 1 3) (by simp) with h4719 | h4719
                            · linarith only [h4625, h4719, hlam]
                            · rcases p4697_3 (m.d 1 4) (by simp) with h4721 | h4721
                              · linarith only [h4626, h4721, hlam]
                              · linarith only [h4628, h4721, hlam]
                          · linarith only [h4625, h4718, hlam]
                        · linarith only [h1, h4717, hlam]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        rcases p4697_3 (m.d 0 1) (by simp) with h4726 | h4726
                        · rcases p4697_3 (m.d 1 2) (by simp) with h4727 | h4727
                          · rcases p4697_3 (m.d 1 3) (by simp) with h4728 | h4728
                            · linarith only [h4625, h4728, hlam]
                            · rcases p4697_3 (m.d 1 4) (by simp) with h4730 | h4730
                              · linarith only [h4626, h4730, hlam]
                              · rcases p4697_3 (m.d 1 5) (by simp) with h4732 | h4732
                                · linarith only [h4627, h4732, hlam]
                                · linarith only [h4632, h4732, hlam]
                          · linarith only [h4626, h4727, hlam]
                        · linarith only [h2, h4726, hlam]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p4697_1, u5ehi1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h1, hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h4625, hlam, p4697_1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h4628, hlam, p4697_1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h4630, hlam, p4697_1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h2, hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h4626, hlam, p4697_1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h2, h4625, h4640, h7, hc23, hc45, hlam, hphi, ht34, p4697_1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h4632, hlam, p4697_1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h3, hlam, p4697_0]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [h4627, hlam, p4697_1]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        rcases p4697_3 (m.d 0 1) (by simp) with h4750 | h4750
                        · rcases p4697_3 (m.d 1 2) (by simp) with h4751 | h4751
                          · rcases p4697_3 (m.d 1 3) (by simp) with h4752 | h4752
                            · linarith only [h4630, h4752, hlam]
                            · rcases p4697_3 (m.d 1 4) (by simp) with h4754 | h4754
                              · linarith only [h4632, h4754, hlam]
                              · linarith only [h4628, h4754, hlam]
                          · linarith only [h4625, h4751, hlam]
                        · linarith only [h1, h4750, hlam]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        rcases p4697_3 (m.d 0 1) (by simp) with h4759 | h4759
                        · rcases p4697_3 (m.d 1 2) (by simp) with h4760 | h4760
                          · rcases p4697_3 (m.d 1 3) (by simp) with h4761 | h4761
                            · linarith only [h4630, h4761, hlam]
                            · rcases p4697_3 (m.d 1 4) (by simp) with h4763 | h4763
                              · linarith only [h4632, h4763, hlam]
                              · rcases p4697_3 (m.d 1 5) (by simp) with h4765 | h4765
                                · rcases h1emax with h4766 | h4766 | h4766 | h4766 | h4766
                                  · linarith only [h3, h4626, h4634, h4766, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4697_1]
                                  · linarith only [h4626, h4627, h4634, h4766, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4697_1]
                                  · rcases h3bigk with h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c | h4769c
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4625, h4640, h7, hc23, hc45, hlam, hphi, ht34, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4640, h7, hc23, hc45, hlam, hphi, ht34, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h7, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h3894, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h1, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h1, h4640, h7, hc23, hc45, hlam, hphi, ht34, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4628, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4630, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4625, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4634, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4636, hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4640, hc03, hc45, hlam, hphi, ht34, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4640, hc13, hc45, hlam, hphi, ht34, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4640, hc23, hc45, hlam, hphi, ht34, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [hlam, p4769_0]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4640, hlam, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      rcases p4769_3 (m.d 0 3) (by simp) with h4790 | h4790
                                      · linarith only [h4790, hlam, p4769_0]
                                      · rcases p4769_3 (m.d 1 3) (by simp) with h4792 | h4792
                                        · linarith only [h4630, h4792, hlam]
                                        · rcases p4769_3 (m.d 2 3) (by simp) with h4794 | h4794
                                          · linarith only [h4636, h4794, hlam]
                                          · rcases p4769_3 (m.d 3 4) (by simp) with h4796 | h4796
                                            · linarith only [h4640, h4796, hlam]
                                            · linarith only [h4796, h7, hlam]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      rcases p4769_3 (m.d 0 3) (by simp) with h4799 | h4799
                                      · linarith only [h3894, h4799, hlam]
                                      · linarith only [h1, h4799, hlam]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      rcases p4769_3 (m.d 0 3) (by simp) with h4802 | h4802
                                      · linarith only [h3894, h4802, hlam]
                                      · linarith only [h4, h4802, hlam]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [h4640, h7, hc03, hc45, hlam, hphi, ht34, p4769_1]
                                    · have p4769_0 := h4769c.1
                                      have p4769_1 := h4769c.2.1
                                      have p4769_2 := h4769c.2.2.1
                                      have p4769_3 := h4769c.2.2.2
                                      linarith only [hlam, p4769_0]
                                  · rcases h3bigk with h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c | h4807c
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4625, h7, hc23, hc34, hlam, hphi, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h7, hc23, hc34, hlam, hphi, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h7, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h3894, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h1, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h1, h7, hc23, hc34, hlam, hphi, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4628, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4630, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4625, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4634, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4636, hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4640, hc03, hc45, hlam, hphi, ht34, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4640, hc13, hc45, hlam, hphi, ht34, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4640, hc23, hc45, hlam, hphi, ht34, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [hlam, p4807_0]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h4640, hlam, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      rcases p4807_3 (m.d 0 3) (by simp) with h4828 | h4828
                                      · linarith only [h4828, hlam, p4807_0]
                                      · rcases p4807_3 (m.d 1 3) (by simp) with h4830 | h4830
                                        · linarith only [h4630, h4830, hlam]
                                        · rcases p4807_3 (m.d 2 3) (by simp) with h4832 | h4832
                                          · linarith only [h4636, h4832, hlam]
                                          · rcases p4807_3 (m.d 3 4) (by simp) with h4834 | h4834
                                            · linarith only [h4640, h4834, hlam]
                                            · linarith only [h4834, h7, hlam]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      rcases p4807_3 (m.d 0 3) (by simp) with h4837 | h4837
                                      · linarith only [h3894, h4837, hlam]
                                      · linarith only [h1, h4837, hlam]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      rcases p4807_3 (m.d 0 3) (by simp) with h4840 | h4840
                                      · linarith only [h3894, h4840, hlam]
                                      · linarith only [h4, h4840, hlam]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [h1, h4625, h4640, h7, hc23, hc45, hlam, hphi, ht34, p4807_1]
                                    · have p4807_0 := h4807c.1
                                      have p4807_1 := h4807c.2.1
                                      have p4807_2 := h4807c.2.2.1
                                      have p4807_3 := h4807c.2.2.2
                                      linarith only [hlam, p4807_0]
                                  · linarith only [h4626, h4634, h4766, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4697_1]
                                · linarith only [h4632, h4765, hlam]
                          · linarith only [h4626, h4760, hlam]
                        · linarith only [h2, h4759, hlam]
                      · have p4697_0 := h4697c.1
                        have p4697_1 := h4697c.2.1
                        have p4697_2 := h4697c.2.2.1
                        have p4697_3 := h4697c.2.2.2
                        linarith only [hlam, p4697_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4850 | h4850
        · linarith only [h1, h4850, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4852 | h4852
          · linarith only [h1, h3894, h4852, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4854 | h4854
            · linarith only [h3981, h4626, h4627, h4854, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4856 | h4856
              · linarith only [h0, h4625, h4627, h4856, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4858 | h4858
                · linarith only [h1, h3894, h4625, h4627, h4858, h6, h7, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4860 | h4860
                  · linarith only [h3981, h4626, h4627, h4860, h6, h7, hc03, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4862 | h4862
                    · linarith only [h3981, h4625, h4627, h4862, h6, hc23, hc34, hlam, hphi]
                    · rcases h1bigk with h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c | h4864c
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        rcases p4864_3 (m.d 0 1) (by simp) with h4866 | h4866
                        · rcases p4864_3 (m.d 1 2) (by simp) with h4867 | h4867
                          · linarith only [h4867, hlam, p4864_0]
                          · rcases p4864_3 (m.d 1 3) (by simp) with h4869 | h4869
                            · linarith only [h1, h4869, hlam]
                            · rcases p4864_3 (m.d 1 4) (by simp) with h4871 | h4871
                              · linarith only [h2, h4871, hlam]
                              · rcases p4864_3 (m.d 1 5) (by simp) with h4873 | h4873
                                · linarith only [h3, h4873, hlam]
                                · linarith only [h4627, h4873, hlam]
                        · linarith only [h4866, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        rcases p4864_3 (m.d 0 1) (by simp) with h4877 | h4877
                        · rcases p4864_3 (m.d 1 2) (by simp) with h4878 | h4878
                          · linarith only [h0, h4878, hlam]
                          · linarith only [h4625, h4878, hlam]
                        · linarith only [h4877, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        rcases p4864_3 (m.d 0 1) (by simp) with h4882 | h4882
                        · rcases p4864_3 (m.d 1 2) (by simp) with h4883 | h4883
                          · linarith only [h0, h4883, hlam]
                          · linarith only [h4626, h4883, hlam]
                        · linarith only [h4882, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        rcases p4864_3 (m.d 0 1) (by simp) with h4887 | h4887
                        · rcases p4864_3 (m.d 1 2) (by simp) with h4888 | h4888
                          · linarith only [h0, h4888, hlam]
                          · rcases p4864_3 (m.d 1 3) (by simp) with h4890 | h4890
                            · linarith only [h1, h4890, hlam]
                            · rcases p4864_3 (m.d 1 4) (by simp) with h4892 | h4892
                              · linarith only [h2, h4892, hlam]
                              · rcases p4864_3 (m.d 1 5) (by simp) with h4894 | h4894
                                · linarith only [h4894, hlam, p4864_0]
                                · rcases h1emax with h4896 | h4896 | h4896 | h4896 | h4896
                                  · linarith only [h0, h4626, h4627, h4856, h4896, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · rcases h3bigk with h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4862, h7, hc13, hc45, hlam, hphi, ht34, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4862, h7, hc23, hc45, hlam, hphi, ht34, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h7, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h3894, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h1, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h1, h4862, h7, hc23, hc45, hlam, hphi, ht34, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4850, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4852, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4625, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4856, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4858, hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4862, hc03, hc45, hlam, hphi, ht34, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4625, h4862, hc23, hc45, hlam, hphi, ht34, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4862, hc23, hc45, hlam, hphi, ht34, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [hlam, p4898_0]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h4862, hlam, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      rcases p4898_3 (m.d 0 3) (by simp) with h4919 | h4919
                                      · linarith only [h4919, hlam, p4898_0]
                                      · rcases p4898_3 (m.d 1 3) (by simp) with h4921 | h4921
                                        · linarith only [h4852, h4921, hlam]
                                        · rcases p4898_3 (m.d 2 3) (by simp) with h4923 | h4923
                                          · linarith only [h4858, h4923, hlam]
                                          · rcases p4898_3 (m.d 3 4) (by simp) with h4925 | h4925
                                            · linarith only [h4862, h4925, hlam]
                                            · linarith only [h4925, h7, hlam]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      rcases p4898_3 (m.d 0 3) (by simp) with h4928 | h4928
                                      · linarith only [h3894, h4928, hlam]
                                      · linarith only [h1, h4928, hlam]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      rcases p4898_3 (m.d 0 3) (by simp) with h4931 | h4931
                                      · linarith only [h3894, h4931, hlam]
                                      · linarith only [h4, h4931, hlam]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [h1, h4625, h4862, h7, hc23, hc45, hlam, hphi, ht34, p4898_1]
                                    · have p4898_0 := h4898c.1
                                      have p4898_1 := h4898c.2.1
                                      have p4898_2 := h4898c.2.2.1
                                      have p4898_3 := h4898c.2.2.2
                                      linarith only [hlam, p4898_0]
                                  · rcases h3bigk with h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c | h4936c
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4625, h7, hc23, hc34, hlam, hphi, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h7, hc23, hc34, hlam, hphi, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h7, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h3894, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h1, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h1, h7, hc23, hc34, hlam, hphi, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4850, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4852, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4625, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4856, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4858, hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4862, hc03, hc45, hlam, hphi, ht34, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4625, h4862, hc23, hc45, hlam, hphi, ht34, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4862, hc23, hc45, hlam, hphi, ht34, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [hlam, p4936_0]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h4862, hlam, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      rcases p4936_3 (m.d 0 3) (by simp) with h4957 | h4957
                                      · linarith only [h4957, hlam, p4936_0]
                                      · rcases p4936_3 (m.d 1 3) (by simp) with h4959 | h4959
                                        · linarith only [h4852, h4959, hlam]
                                        · rcases p4936_3 (m.d 2 3) (by simp) with h4961 | h4961
                                          · linarith only [h4858, h4961, hlam]
                                          · rcases p4936_3 (m.d 3 4) (by simp) with h4963 | h4963
                                            · linarith only [h4862, h4963, hlam]
                                            · linarith only [h4963, h7, hlam]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      rcases p4936_3 (m.d 0 3) (by simp) with h4966 | h4966
                                      · linarith only [h3894, h4966, hlam]
                                      · linarith only [h1, h4966, hlam]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      rcases p4936_3 (m.d 0 3) (by simp) with h4969 | h4969
                                      · linarith only [h3894, h4969, hlam]
                                      · linarith only [h4, h4969, hlam]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [h1, h4625, h4862, h7, hc23, hc45, hlam, hphi, ht34, p4936_1]
                                    · have p4936_0 := h4936c.1
                                      have p4936_1 := h4936c.2.1
                                      have p4936_2 := h4936c.2.2.1
                                      have p4936_3 := h4936c.2.2.2
                                      linarith only [hlam, p4936_0]
                                  · rcases h3bigk with h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4625, h7, hc23, hc34, hlam, hphi, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h7, hc23, hc34, hlam, hphi, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h7, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h3894, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h1, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h1, h7, hc23, hc34, hlam, hphi, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4850, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4852, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4625, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4856, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4858, hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4862, hc03, hc45, hlam, hphi, ht34, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4625, h4862, hc23, hc45, hlam, hphi, ht34, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4862, hc23, hc45, hlam, hphi, ht34, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [hlam, p4974_0]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h4862, hlam, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      rcases p4974_3 (m.d 0 3) (by simp) with h4995 | h4995
                                      · linarith only [h4995, hlam, p4974_0]
                                      · rcases p4974_3 (m.d 1 3) (by simp) with h4997 | h4997
                                        · linarith only [h4852, h4997, hlam]
                                        · rcases p4974_3 (m.d 2 3) (by simp) with h4999 | h4999
                                          · linarith only [h4858, h4999, hlam]
                                          · rcases p4974_3 (m.d 3 4) (by simp) with h5001 | h5001
                                            · linarith only [h4862, h5001, hlam]
                                            · linarith only [h5001, h7, hlam]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      rcases p4974_3 (m.d 0 3) (by simp) with h5004 | h5004
                                      · linarith only [h3894, h5004, hlam]
                                      · linarith only [h1, h5004, hlam]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      rcases p4974_3 (m.d 0 3) (by simp) with h5007 | h5007
                                      · linarith only [h3894, h5007, hlam]
                                      · linarith only [h4, h5007, hlam]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [h1, h4625, h4862, h7, hc23, hc45, hlam, hphi, ht34, p4974_1]
                                    · have p4974_0 := h4974c.1
                                      have p4974_1 := h4974c.2.1
                                      have p4974_2 := h4974c.2.2.1
                                      have p4974_3 := h4974c.2.2.2
                                      linarith only [hlam, p4974_0]
                                  · rcases h3bigk with h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c | h5012c
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4625, h7, hc23, hc34, hlam, hphi, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h7, hc23, hc34, hlam, hphi, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h7, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h3894, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h1, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h1, h7, hc23, hc34, hlam, hphi, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4850, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4852, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4625, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4856, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4858, hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4862, hc03, hc45, hlam, hphi, ht34, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4625, h4862, hc23, hc45, hlam, hphi, ht34, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4862, hc23, hc45, hlam, hphi, ht34, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [hlam, p5012_0]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h4862, hlam, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      rcases p5012_3 (m.d 0 3) (by simp) with h5033 | h5033
                                      · linarith only [h5033, hlam, p5012_0]
                                      · rcases p5012_3 (m.d 1 3) (by simp) with h5035 | h5035
                                        · linarith only [h4852, h5035, hlam]
                                        · rcases p5012_3 (m.d 2 3) (by simp) with h5037 | h5037
                                          · linarith only [h4858, h5037, hlam]
                                          · rcases p5012_3 (m.d 3 4) (by simp) with h5039 | h5039
                                            · linarith only [h4862, h5039, hlam]
                                            · linarith only [h5039, h7, hlam]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      rcases p5012_3 (m.d 0 3) (by simp) with h5042 | h5042
                                      · linarith only [h3894, h5042, hlam]
                                      · linarith only [h1, h5042, hlam]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      rcases p5012_3 (m.d 0 3) (by simp) with h5045 | h5045
                                      · linarith only [h3894, h5045, hlam]
                                      · linarith only [h4, h5045, hlam]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [h1, h4625, h4862, h7, hc23, hc45, hlam, hphi, ht34, p5012_1]
                                    · have p5012_0 := h5012c.1
                                      have p5012_1 := h5012c.2.1
                                      have p5012_2 := h5012c.2.2.1
                                      have p5012_3 := h5012c.2.2.2
                                      linarith only [hlam, p5012_0]
                        · linarith only [h4887, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h0, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h0, h4625, h4627, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h0, h4627, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h4627, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h1, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h4625, hlam, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h4850, hlam, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h4852, hlam, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h2, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h4626, hlam, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h2, h3981, h4625, hc23, hc45, hlam, hphi, ht34, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h4854, hlam, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h3, hlam, p4864_0]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [h3, h3894, h4625, h4862, hc23, hc45, hlam, hphi, ht34, p4864_1]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        rcases p4864_3 (m.d 0 1) (by simp) with h5068 | h5068
                        · rcases p4864_3 (m.d 1 2) (by simp) with h5069 | h5069
                          · linarith only [h4627, h5069, hlam]
                          · linarith only [h4625, h5069, hlam]
                        · linarith only [h1, h5068, hlam]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        rcases p4864_3 (m.d 0 1) (by simp) with h5073 | h5073
                        · rcases p4864_3 (m.d 1 2) (by simp) with h5074 | h5074
                          · linarith only [h4627, h5074, hlam]
                          · linarith only [h4626, h5074, hlam]
                        · linarith only [h2, h5073, hlam]
                      · have p4864_0 := h4864c.1
                        have p4864_1 := h4864c.2.1
                        have p4864_2 := h4864c.2.2.1
                        have p4864_3 := h4864c.2.2.2
                        linarith only [hlam, p4864_0]
    · linarith only [h3981, h4625, h4626, h5, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5080 | h5080
    · linarith only [h3981, h4, h4625, h5080, h7, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5082 | h5082
      · linarith only [h3981, h4, h4625, h5082, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5084 | h5084
        · linarith only [h4, h4625, h5084, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5086 | h5086
          · linarith only [h3894, h4, h4625, h5086, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5088 | h5088
            · linarith only [h3981, h4, h4625, h5080, h5088, h7, hc12, hc24, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5090 | h5090
              · linarith only [h4, h5090, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5092 | h5092
                · linarith only [h3894, h4, h5092, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5094 | h5094
                  · linarith only [h3981, h5, h5094, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5096 | h5096
                    · linarith only [h3981, h4, h4625, h5096, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h4625, h5096, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 10184000 in
set_option maxHeartbeats 10184000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3894 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h3981 | h3981
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h3894 h3981
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h3894 h3981

set_option maxHeartbeats 10184000 in
set_option maxHeartbeats 10184000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s6_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h3894 | h3894
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h3894
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h3894

set_option maxHeartbeats 10184000 in
set_option maxHeartbeats 10184000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s6_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s6_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7

end R2N4
