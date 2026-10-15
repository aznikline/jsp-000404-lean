import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h12243 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h12244 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h12245 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 2 3 5 (by decide) (by decide) with h12596 | h12596
  · linarith only [h12233, h12236, h12245, h12596, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h12598 | h12598
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12599 | h12599
      · rcases h1bigk with h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c | h12600c
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h0, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h10472, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h11379, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12013, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          rcases p12600_3 (m.d 0 1) (by simp) with h12606 | h12606
          · linarith only [h12606, hlam, p12600_0]
          · rcases p12600_3 (m.d 1 2) (by simp) with h12608 | h12608
            · rcases p12600_3 (m.d 1 3) (by simp) with h12609 | h12609
              · linarith only [h12239, h12609, hlam]
              · linarith only [h10472, h12609, hlam]
            · linarith only [h12608, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h10472, h12236, h12596, h12599, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h11379, hc01, hc12, hlam, hphi, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12013, hc01, hc12, hlam, hphi, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          rcases p12600_3 (m.d 0 1) (by simp) with h12617 | h12617
          · linarith only [h12617, hlam, p12600_0]
          · rcases p12600_3 (m.d 1 2) (by simp) with h12619 | h12619
            · rcases p12600_3 (m.d 1 3) (by simp) with h12620 | h12620
              · rcases p12600_3 (m.d 1 4) (by simp) with h12621 | h12621
                · linarith only [h12242, h12621, hlam]
                · linarith only [h11379, h12621, hlam]
              · linarith only [h12620, hlam, p12600_0]
            · linarith only [h0, h12619, hlam]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12239, hlam, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h11379, h12236, h12245, h12598, hc13, hlam, hphi, ht01, ht0b, ht5b, p12600_1, u5ehi4]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12013, h12239, hc01, hc12, hlam, hphi, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          rcases p12600_3 (m.d 0 1) (by simp) with h12630 | h12630
          · linarith only [h12630, hlam, p12600_0]
          · rcases p12600_3 (m.d 1 2) (by simp) with h12632 | h12632
            · rcases p12600_3 (m.d 1 3) (by simp) with h12633 | h12633
              · rcases p12600_3 (m.d 1 4) (by simp) with h12634 | h12634
                · rcases p12600_3 (m.d 1 5) (by simp) with h12635 | h12635
                  · linarith only [h12244, h12635, hlam]
                  · linarith only [h12013, h12635, hlam]
                · linarith only [h12634, hlam, p12600_0]
              · linarith only [h10472, h12633, hlam]
            · linarith only [h0, h12632, hlam]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12240, hlam, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12242, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12013, hc01, hc14, hlam, hphi, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          rcases p12600_3 (m.d 0 1) (by simp) with h12645 | h12645
          · linarith only [h12645, hlam, p12600_0]
          · rcases p12600_3 (m.d 1 2) (by simp) with h12647 | h12647
            · rcases p12600_3 (m.d 1 3) (by simp) with h12648 | h12648
              · rcases p12600_3 (m.d 1 4) (by simp) with h12649 | h12649
                · rcases p12600_3 (m.d 1 5) (by simp) with h12650 | h12650
                  · rcases h1emax with h12651 | h12651 | h12651 | h12651 | h12651
                    · rcases h3bigk with h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c | h12652c
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h10472, hlam, p12652_1]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        rcases p12652_3 (m.d 0 3) (by simp) with h12655 | h12655
                        · rcases p12652_3 (m.d 1 3) (by simp) with h12656 | h12656
                          · rcases p12652_3 (m.d 2 3) (by simp) with h12657 | h12657
                            · linarith only [h12233, h12657, hlam]
                            · rcases p12652_3 (m.d 3 4) (by simp) with h12659 | h12659
                              · linarith only [h12236, h12659, hlam]
                              · linarith only [h12245, h12659, hlam]
                          · linarith only [h12239, h12656, hlam]
                        · linarith only [h12233, h12655, hlam]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12233, h12245, h12598, hc02, hlam, hphi, ht0b, ht5b, p12652_1, u5ehi4]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        rcases p12652_3 (m.d 0 3) (by simp) with h12665 | h12665
                        · rcases p12652_3 (m.d 1 3) (by simp) with h12666 | h12666
                          · rcases p12652_3 (m.d 2 3) (by simp) with h12667 | h12667
                            · linarith only [h12233, h12667, hlam]
                            · rcases p12652_3 (m.d 3 4) (by simp) with h12669 | h12669
                              · linarith only [h12236, h12669, hlam]
                              · linarith only [h12599, h12669, hlam]
                          · linarith only [h12243, h12666, hlam]
                        · linarith only [h12665, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12236, h12239, h12245, h12598, hc12, hlam, hphi, ht01, ht0b, ht5b, p12652_1, u5ehi4]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        rcases p12652_3 (m.d 0 3) (by simp) with h12676 | h12676
                        · linarith only [h10472, h12676, hlam]
                        · linarith only [h12233, h12676, hlam]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12245, h12598, hc13, hlam, hphi, ht01, ht0b, ht5b, p12652_1, u5ehi4]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        rcases p12652_3 (m.d 0 3) (by simp) with h12680 | h12680
                        · linarith only [h10472, h12680, hlam]
                        · linarith only [h12237, h12680, hlam]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12233, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12239, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12245, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12596, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12236, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12242, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        rcases p12652_3 (m.d 0 3) (by simp) with h12690 | h12690
                        · rcases p12652_3 (m.d 1 3) (by simp) with h12691 | h12691
                          · rcases p12652_3 (m.d 2 3) (by simp) with h12692 | h12692
                            · linarith only [h12692, hlam, p12652_0]
                            · rcases p12652_3 (m.d 3 4) (by simp) with h12694 | h12694
                              · rcases p12652_3 (m.d 3 5) (by simp) with h12695 | h12695
                                · linarith only [h12599, h12695, hlam]
                                · linarith only [h12596, h12695, hlam]
                              · linarith only [h12694, hlam, p12652_0]
                          · linarith only [h12239, h12691, hlam]
                        · linarith only [h12233, h12690, hlam]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12236, hc03, hlam, hphi, ht0b, ht5b, p12652_1, u5ehi3]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12237, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12243, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        rcases p12652_3 (m.d 0 3) (by simp) with h12705 | h12705
                        · rcases p12652_3 (m.d 1 3) (by simp) with h12706 | h12706
                          · rcases p12652_3 (m.d 2 3) (by simp) with h12707 | h12707
                            · linarith only [h12707, hlam, p12652_0]
                            · rcases p12652_3 (m.d 3 4) (by simp) with h12709 | h12709
                              · rcases p12652_3 (m.d 3 5) (by simp) with h12710 | h12710
                                · rcases h5bigk with h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c | h12711c
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12013, hlam, p12711_1]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    rcases p12711_3 (m.d 0 5) (by simp) with h12714 | h12714
                                    · rcases p12711_3 (m.d 1 5) (by simp) with h12715 | h12715
                                      · rcases p12711_3 (m.d 2 5) (by simp) with h12716 | h12716
                                        · linarith only [h12235, h12716, hlam]
                                        · rcases p12711_3 (m.d 3 5) (by simp) with h12718 | h12718
                                          · linarith only [h12237, h12718, hlam]
                                          · linarith only [h12596, h12718, hlam]
                                      · linarith only [h12241, h12715, hlam]
                                    · linarith only [h12235, h12714, hlam]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12238, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12652_1, p12711_1]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    rcases p12711_3 (m.d 0 5) (by simp) with h12724 | h12724
                                    · rcases p12711_3 (m.d 1 5) (by simp) with h12725 | h12725
                                      · rcases p12711_3 (m.d 2 5) (by simp) with h12726 | h12726
                                        · linarith only [h12235, h12726, hlam]
                                        · linarith only [h12598, h12726, hlam]
                                      · linarith only [h12244, h12725, hlam]
                                    · linarith only [h12238, h12724, hlam]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12237, h12239, h12242, h12244, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12652_1, p12711_1]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    rcases p12711_3 (m.d 0 5) (by simp) with h12733 | h12733
                                    · linarith only [h12013, h12733, hlam]
                                    · linarith only [h12235, h12733, hlam]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12239, h12242, h12244, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12652_1, p12711_1]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    rcases p12711_3 (m.d 0 5) (by simp) with h12737 | h12737
                                    · linarith only [h12013, h12737, hlam]
                                    · linarith only [h12238, h12737, hlam]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12235, hlam, p12711_1]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12241, hlam, p12711_1]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12596, hlam, p12711_1]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h0, h12235, hc12, hlam, hphi, ht01, ht0b, ht5b, p12711_1, u5ehi4]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12237, hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12243, hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h10472, h12237, h12239, hc12, hlam, hphi, ht01, ht0b, ht5b, p12711_1, u5ehi2]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h10472, h12236, h12239, h12599, hc12, hlam, hphi, ht01, ht0b, ht5b, p12711_1, u5ehi4]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12238, hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12244, hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12598, hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [h12599, hlam, p12711_0]
                                  · have p12711_0 := h12711c.1
                                    have p12711_1 := h12711c.2.1
                                    have p12711_2 := h12711c.2.2.1
                                    have p12711_3 := h12711c.2.2.2
                                    linarith only [hlam, p12711_0]
                                · linarith only [h12710, hlam, p12652_0]
                              · linarith only [h12245, h12709, hlam]
                          · linarith only [h12239, h12706, hlam]
                        · linarith only [h12233, h12705, hlam]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [h12599, hlam, p12652_0]
                      · have p12652_0 := h12652c.1
                        have p12652_1 := h12652c.2.1
                        have p12652_2 := h12652c.2.2.1
                        have p12652_3 := h12652c.2.2.2
                        linarith only [hlam, p12652_0]
                    · linarith only [h10472, h12236, h12239, h12599, h12651, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h10472, h12236, h12245, h12598, h12651, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h12244, h12651, hc01, hlam, p12600_1]
                    · linarith only [h12651, hc01, hlam, p12600_1]
                  · linarith only [h12650, hlam, p12600_0]
                · linarith only [h11379, h12649, hlam]
              · linarith only [h10472, h12648, hlam]
            · linarith only [h0, h12647, hlam]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12241, hlam, p12600_1]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12243, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [h12244, hlam, p12600_0]
        · have p12600_0 := h12600c.1
          have p12600_1 := h12600c.2.1
          have p12600_2 := h12600c.2.2.1
          have p12600_3 := h12600c.2.2.2
          linarith only [hlam, p12600_0]
      · linarith only [h12245, h12598, h12599, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12774 | h12774
      · rcases h1bigk with h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c | h12775c
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h0, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h10472, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h11379, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12013, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          rcases p12775_3 (m.d 0 1) (by simp) with h12781 | h12781
          · linarith only [h12781, hlam, p12775_0]
          · rcases p12775_3 (m.d 1 2) (by simp) with h12783 | h12783
            · rcases p12775_3 (m.d 1 3) (by simp) with h12784 | h12784
              · linarith only [h12239, h12784, hlam]
              · linarith only [h10472, h12784, hlam]
            · linarith only [h12783, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h10472, h12236, h12598, h12774, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h11379, hc01, hc12, hlam, hphi, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12013, hc01, hc12, hlam, hphi, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          rcases p12775_3 (m.d 0 1) (by simp) with h12792 | h12792
          · linarith only [h12792, hlam, p12775_0]
          · rcases p12775_3 (m.d 1 2) (by simp) with h12794 | h12794
            · rcases p12775_3 (m.d 1 3) (by simp) with h12795 | h12795
              · rcases p12775_3 (m.d 1 4) (by simp) with h12796 | h12796
                · linarith only [h12242, h12796, hlam]
                · linarith only [h11379, h12796, hlam]
              · linarith only [h12795, hlam, p12775_0]
            · linarith only [h0, h12794, hlam]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12239, hlam, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h11379, h12236, h12245, h12598, h12774, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12013, h12239, hc01, hc12, hlam, hphi, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          rcases p12775_3 (m.d 0 1) (by simp) with h12805 | h12805
          · linarith only [h12805, hlam, p12775_0]
          · rcases p12775_3 (m.d 1 2) (by simp) with h12807 | h12807
            · rcases p12775_3 (m.d 1 3) (by simp) with h12808 | h12808
              · rcases p12775_3 (m.d 1 4) (by simp) with h12809 | h12809
                · rcases p12775_3 (m.d 1 5) (by simp) with h12810 | h12810
                  · linarith only [h12244, h12810, hlam]
                  · linarith only [h12013, h12810, hlam]
                · linarith only [h12809, hlam, p12775_0]
              · linarith only [h10472, h12808, hlam]
            · linarith only [h0, h12807, hlam]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12240, hlam, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12242, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12013, hc01, hc14, hlam, hphi, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          rcases p12775_3 (m.d 0 1) (by simp) with h12820 | h12820
          · linarith only [h12820, hlam, p12775_0]
          · rcases p12775_3 (m.d 1 2) (by simp) with h12822 | h12822
            · rcases p12775_3 (m.d 1 3) (by simp) with h12823 | h12823
              · rcases p12775_3 (m.d 1 4) (by simp) with h12824 | h12824
                · rcases p12775_3 (m.d 1 5) (by simp) with h12825 | h12825
                  · rcases h1emax with h12826 | h12826 | h12826 | h12826 | h12826
                    · rcases h3bigk with h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c | h12827c
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h10472, hlam, p12827_1]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12236, h12245, h12598, h12774, hlam, p12827_2]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12245, h12598, h12774, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12827_1]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        rcases p12827_3 (m.d 0 3) (by simp) with h12832 | h12832
                        · rcases p12827_3 (m.d 1 3) (by simp) with h12833 | h12833
                          · rcases p12827_3 (m.d 2 3) (by simp) with h12834 | h12834
                            · linarith only [h12233, h12834, hlam]
                            · rcases p12827_3 (m.d 3 4) (by simp) with h12836 | h12836
                              · linarith only [h12236, h12836, hlam]
                              · linarith only [h12774, h12836, hlam]
                          · linarith only [h12243, h12833, hlam]
                        · linarith only [h12832, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12236, h12239, h12245, h12598, h12774, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12827_1]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h10472, h12236, h12245, h12598, h12774, hlam, p12827_2]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12245, h12598, h12774, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12827_1]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        rcases p12827_3 (m.d 0 3) (by simp) with h12845 | h12845
                        · linarith only [h10472, h12845, hlam]
                        · linarith only [h12237, h12845, hlam]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12233, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12239, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12245, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12596, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12236, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12242, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        rcases p12827_3 (m.d 0 3) (by simp) with h12855 | h12855
                        · rcases p12827_3 (m.d 1 3) (by simp) with h12856 | h12856
                          · rcases p12827_3 (m.d 2 3) (by simp) with h12857 | h12857
                            · linarith only [h12857, hlam, p12827_0]
                            · rcases p12827_3 (m.d 3 4) (by simp) with h12859 | h12859
                              · rcases p12827_3 (m.d 3 5) (by simp) with h12860 | h12860
                                · linarith only [h12774, h12860, hlam]
                                · linarith only [h12596, h12860, hlam]
                              · linarith only [h12859, hlam, p12827_0]
                          · linarith only [h12239, h12856, hlam]
                        · linarith only [h12233, h12855, hlam]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12236, h12245, h12598, h12774, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12827_1]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12237, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12243, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        rcases p12827_3 (m.d 0 3) (by simp) with h12870 | h12870
                        · rcases p12827_3 (m.d 1 3) (by simp) with h12871 | h12871
                          · rcases p12827_3 (m.d 2 3) (by simp) with h12872 | h12872
                            · linarith only [h12872, hlam, p12827_0]
                            · rcases p12827_3 (m.d 3 4) (by simp) with h12874 | h12874
                              · rcases p12827_3 (m.d 3 5) (by simp) with h12875 | h12875
                                · rcases h5bigk with h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c | h12876c
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12013, hlam, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    rcases p12876_3 (m.d 0 5) (by simp) with h12879 | h12879
                                    · rcases p12876_3 (m.d 1 5) (by simp) with h12880 | h12880
                                      · rcases p12876_3 (m.d 2 5) (by simp) with h12881 | h12881
                                        · linarith only [h12235, h12881, hlam]
                                        · rcases p12876_3 (m.d 3 5) (by simp) with h12883 | h12883
                                          · linarith only [h12237, h12883, hlam]
                                          · linarith only [h12596, h12883, hlam]
                                      · linarith only [h12241, h12880, hlam]
                                    · linarith only [h12235, h12879, hlam]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12238, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12827_1, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    rcases p12876_3 (m.d 0 5) (by simp) with h12889 | h12889
                                    · rcases p12876_3 (m.d 1 5) (by simp) with h12890 | h12890
                                      · rcases p12876_3 (m.d 2 5) (by simp) with h12891 | h12891
                                        · linarith only [h12235, h12891, hlam]
                                        · rcases p12876_3 (m.d 3 5) (by simp) with h12893 | h12893
                                          · linarith only [h12237, h12893, hlam]
                                          · linarith only [h12774, h12893, hlam]
                                      · linarith only [h12244, h12890, hlam]
                                    · linarith only [h12238, h12889, hlam]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12237, h12239, h12242, h12244, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12827_1, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    rcases p12876_3 (m.d 0 5) (by simp) with h12900 | h12900
                                    · linarith only [h12013, h12900, hlam]
                                    · linarith only [h12235, h12900, hlam]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12239, h12242, h12244, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12827_1, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    rcases p12876_3 (m.d 0 5) (by simp) with h12904 | h12904
                                    · linarith only [h12013, h12904, hlam]
                                    · linarith only [h12238, h12904, hlam]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12235, hlam, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12241, hlam, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12596, hlam, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12598, hlam, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12237, hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12243, hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h10472, h12237, h12239, hc12, hlam, hphi, ht01, ht0b, ht5b, p12876_1, u5ehi2]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h10472, h12236, h12239, h12245, h12598, h12774, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12876_1]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12238, hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12244, hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h11379, h12238, h12239, h12242, hc12, hlam, hphi, ht01, ht0b, ht5b, p12876_1, u5ehi2]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [h12774, hlam, p12876_0]
                                  · have p12876_0 := h12876c.1
                                    have p12876_1 := h12876c.2.1
                                    have p12876_2 := h12876c.2.2.1
                                    have p12876_3 := h12876c.2.2.2
                                    linarith only [hlam, p12876_0]
                                · linarith only [h12875, hlam, p12827_0]
                              · linarith only [h12245, h12874, hlam]
                          · linarith only [h12239, h12871, hlam]
                        · linarith only [h12233, h12870, hlam]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [h12774, hlam, p12827_0]
                      · have p12827_0 := h12827c.1
                        have p12827_1 := h12827c.2.1
                        have p12827_2 := h12827c.2.2.1
                        have p12827_3 := h12827c.2.2.2
                        linarith only [hlam, p12827_0]
                    · linarith only [h10472, h12236, h12239, h12774, h12826, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h10472, h12236, h12245, h12598, h12774, h12826, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h11379, h12826, hc01, hlam]
                    · linarith only [h12826, hc01, hlam, p12775_1]
                  · linarith only [h12825, hlam, p12775_0]
                · linarith only [h11379, h12824, hlam]
              · linarith only [h10472, h12823, hlam]
            · linarith only [h0, h12822, hlam]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12241, hlam, p12775_1]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12243, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [h12244, hlam, p12775_0]
        · have p12775_0 := h12775c.1
          have p12775_1 := h12775c.2.1
          have p12775_2 := h12775c.2.2.1
          have p12775_3 := h12775c.2.2.2
          linarith only [hlam, p12775_0]
      · rcases h1bigk with h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c | h12940c
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h0, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h10472, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h11379, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12013, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          rcases p12940_3 (m.d 0 1) (by simp) with h12946 | h12946
          · linarith only [h12946, hlam, p12940_0]
          · rcases p12940_3 (m.d 1 2) (by simp) with h12948 | h12948
            · rcases p12940_3 (m.d 1 3) (by simp) with h12949 | h12949
              · linarith only [h12239, h12949, hlam]
              · linarith only [h10472, h12949, hlam]
            · linarith only [h12948, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h10472, h12236, h12238, h12774, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h11379, hc01, hc12, hlam, hphi, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12013, hc01, hc12, hlam, hphi, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          rcases p12940_3 (m.d 0 1) (by simp) with h12957 | h12957
          · linarith only [h12957, hlam, p12940_0]
          · rcases p12940_3 (m.d 1 2) (by simp) with h12959 | h12959
            · rcases p12940_3 (m.d 1 3) (by simp) with h12960 | h12960
              · rcases p12940_3 (m.d 1 4) (by simp) with h12961 | h12961
                · linarith only [h12242, h12961, hlam]
                · linarith only [h11379, h12961, hlam]
              · linarith only [h12960, hlam, p12940_0]
            · linarith only [h0, h12959, hlam]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12239, hlam, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h11379, h12238, h12245, h12774, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12013, h12238, h12239, h12245, h12774, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          rcases p12940_3 (m.d 0 1) (by simp) with h12970 | h12970
          · linarith only [h12970, hlam, p12940_0]
          · rcases p12940_3 (m.d 1 2) (by simp) with h12972 | h12972
            · rcases p12940_3 (m.d 1 3) (by simp) with h12973 | h12973
              · rcases p12940_3 (m.d 1 4) (by simp) with h12974 | h12974
                · rcases p12940_3 (m.d 1 5) (by simp) with h12975 | h12975
                  · linarith only [h12244, h12975, hlam]
                  · linarith only [h12013, h12975, hlam]
                · linarith only [h12974, hlam, p12940_0]
              · linarith only [h10472, h12973, hlam]
            · linarith only [h0, h12972, hlam]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12240, hlam, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12242, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12013, h12238, h12245, h12774, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          rcases p12940_3 (m.d 0 1) (by simp) with h12985 | h12985
          · linarith only [h12985, hlam, p12940_0]
          · rcases p12940_3 (m.d 1 2) (by simp) with h12987 | h12987
            · rcases p12940_3 (m.d 1 3) (by simp) with h12988 | h12988
              · rcases p12940_3 (m.d 1 4) (by simp) with h12989 | h12989
                · rcases p12940_3 (m.d 1 5) (by simp) with h12990 | h12990
                  · rcases h1emax with h12991 | h12991 | h12991 | h12991 | h12991
                    · rcases h3bigk with h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c | h12992c
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h10472, hlam, p12992_1]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12236, h12238, h12245, h12774, hlam, p12992_2]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        rcases p12992_3 (m.d 0 3) (by simp) with h12996 | h12996
                        · rcases p12992_3 (m.d 1 3) (by simp) with h12997 | h12997
                          · rcases p12992_3 (m.d 2 3) (by simp) with h12998 | h12998
                            · linarith only [h12233, h12998, hlam]
                            · rcases p12992_3 (m.d 3 4) (by simp) with h13000 | h13000
                              · linarith only [h13000, hlam, p12992_0]
                              · rcases p12992_3 (m.d 3 5) (by simp) with h13002 | h13002
                                · linarith only [h12237, h13002, hlam]
                                · linarith only [h12774, h13002, hlam]
                          · linarith only [h12242, h12997, hlam]
                        · linarith only [h12996, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        rcases p12992_3 (m.d 0 3) (by simp) with h13007 | h13007
                        · rcases p12992_3 (m.d 1 3) (by simp) with h13008 | h13008
                          · rcases p12992_3 (m.d 2 3) (by simp) with h13009 | h13009
                            · linarith only [h12233, h13009, hlam]
                            · rcases p12992_3 (m.d 3 4) (by simp) with h13011 | h13011
                              · linarith only [h12236, h13011, hlam]
                              · rcases p12992_3 (m.d 3 5) (by simp) with h13013 | h13013
                                · linarith only [h13013, hlam, p12992_0]
                                · rcases h5bigk with h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c | h13015c
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12013, hlam, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    rcases p13015_3 (m.d 0 5) (by simp) with h13018 | h13018
                                    · rcases p13015_3 (m.d 1 5) (by simp) with h13019 | h13019
                                      · rcases p13015_3 (m.d 2 5) (by simp) with h13020 | h13020
                                        · linarith only [h12235, h13020, hlam]
                                        · rcases p13015_3 (m.d 3 5) (by simp) with h13022 | h13022
                                          · linarith only [h12237, h13022, hlam]
                                          · linarith only [h12596, h13022, hlam]
                                      · linarith only [h12241, h13019, hlam]
                                    · linarith only [h12235, h13018, hlam]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    rcases p13015_3 (m.d 0 5) (by simp) with h13027 | h13027
                                    · rcases p13015_3 (m.d 1 5) (by simp) with h13028 | h13028
                                      · rcases p13015_3 (m.d 2 5) (by simp) with h13029 | h13029
                                        · linarith only [h12235, h13029, hlam]
                                        · rcases p13015_3 (m.d 3 5) (by simp) with h13031 | h13031
                                          · linarith only [h12237, h13031, hlam]
                                          · rcases p13015_3 (m.d 4 5) (by simp) with h13033 | h13033
                                            · linarith only [h12238, h13033, hlam]
                                            · linarith only [h12774, h13033, hlam]
                                      · linarith only [h12243, h13028, hlam]
                                    · linarith only [h12237, h13027, hlam]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12238, h12245, h12774, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12238, h12245, h12774, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    rcases p13015_3 (m.d 0 5) (by simp) with h13041 | h13041
                                    · linarith only [h12013, h13041, hlam]
                                    · linarith only [h12235, h13041, hlam]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    rcases p13015_3 (m.d 0 5) (by simp) with h13044 | h13044
                                    · linarith only [h12013, h13044, hlam]
                                    · linarith only [h12237, h13044, hlam]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12239, h12242, h12244, h12245, h12774, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12235, hlam, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12241, hlam, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12596, hlam, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12598, hlam, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12237, hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12243, hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h10472, h12239, hc12, hlam, hphi, ht01, ht0b, ht5b, p12992_1, p13015_1, u5ehi2]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12774, hlam, p13015_1]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12238, hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h12244, hlam, p13015_0]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h11379, h12238, h12239, h12242, hc12, hlam, hphi, ht01, ht0b, ht5b, p13015_1, u5ehi2]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [h11379, h12238, h12239, h12242, hc12, hlam, hphi, ht01, ht0b, ht5b, p13015_1, u5ehi3]
                                  · have p13015_0 := h13015c.1
                                    have p13015_1 := h13015c.2.1
                                    have p13015_2 := h13015c.2.2.1
                                    have p13015_3 := h13015c.2.2.2
                                    linarith only [hlam, p13015_0]
                          · linarith only [h12243, h13008, hlam]
                        · linarith only [h13007, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12236, h12239, h12245, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12992_1]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h11379, h12238, h12242, h12245, h12774, hlam, p12992_2]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        rcases p12992_3 (m.d 0 3) (by simp) with h13068 | h13068
                        · linarith only [h10472, h13068, hlam]
                        · linarith only [h12236, h13068, hlam]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        rcases p12992_3 (m.d 0 3) (by simp) with h13071 | h13071
                        · linarith only [h10472, h13071, hlam]
                        · linarith only [h12237, h13071, hlam]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12233, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12239, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12245, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12596, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12236, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12242, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h11379, h12238, h12239, h12242, h12774, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12992_1]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12774, hlam, p12992_1]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12237, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12243, hlam, p12992_0]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        rcases p12992_3 (m.d 0 3) (by simp) with h13086 | h13086
                        · rcases p12992_3 (m.d 1 3) (by simp) with h13087 | h13087
                          · rcases p12992_3 (m.d 2 3) (by simp) with h13088 | h13088
                            · linarith only [h13088, hlam, p12992_0]
                            · rcases p12992_3 (m.d 3 4) (by simp) with h13090 | h13090
                              · linarith only [h12774, h13090, hlam]
                              · linarith only [h12245, h13090, hlam]
                          · linarith only [h12239, h13087, hlam]
                        · linarith only [h12233, h13086, hlam]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [h12245, hc23, hc35, hlam, hphi, p12992_1]
                      · have p12992_0 := h12992c.1
                        have p12992_1 := h12992c.2.1
                        have p12992_2 := h12992c.2.2.1
                        have p12992_3 := h12992c.2.2.2
                        linarith only [hlam, p12992_0]
                    · linarith only [h11379, h12238, h12239, h12242, h12774, h12991, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h10472, h12236, h12238, h12245, h12774, h12991, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h11379, h12238, h12245, h12774, h12991, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h12991, hc01, hlam, p12940_1]
                  · linarith only [h12990, hlam, p12940_0]
                · linarith only [h11379, h12989, hlam]
              · linarith only [h10472, h12988, hlam]
            · linarith only [h0, h12987, hlam]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12241, hlam, p12940_1]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12243, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [h12244, hlam, p12940_0]
        · have p12940_0 := h12940c.1
          have p12940_1 := h12940c.2.1
          have p12940_2 := h12940c.2.2.1
          have p12940_3 := h12940c.2.2.2
          linarith only [hlam, p12940_0]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h12243 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h12244 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 2 3 4 (by decide) (by decide) with h12245 | h12245
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242 h12243 h12244 h12245
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242 h12243 h12244 h12245

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h12243 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h12244 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  linarith only [h11379, h12238, h12244, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h12243 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 1 4 5 (by decide) (by decide) with h12244 | h12244
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242 h12243 h12244
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242 h12243 h12244

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h12243 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  linarith only [h10472, h12237, h12243, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 1 3 5 (by decide) (by decide) with h12243 | h12243
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242 h12243
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242 h12243

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12242 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  linarith only [h10472, h12236, h12242, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 1 3 4 (by decide) (by decide) with h12242 | h12242
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241 h12242

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12241 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  linarith only [h0, h12235, h12241, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 1 2 5 (by decide) (by decide) with h12241 | h12241
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240 h12241

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h12240 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  linarith only [h0, h12234, h12240, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 1 2 4 (by decide) (by decide) with h12240 | h12240
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239 h12240

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h12239 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  linarith only [h0, h12233, h12239, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 1 2 3 (by decide) (by decide) with h12239 | h12239
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238 h12239

end R2N4
