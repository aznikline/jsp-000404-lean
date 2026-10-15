import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11652 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11653 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11654 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11655 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11656 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11657 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11658 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h11659 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 3 5 (by decide) (by decide) with h11660 | h11660
  · rcases m.htr 2 4 5 (by decide) (by decide) with h11661 | h11661
    · rcases m.htr 3 4 5 (by decide) (by decide) with h11662 | h11662
      · rcases h2bigk with h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c | h11663c
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h0, hlam, p11663_1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11659, h11662, hc02, hc45, hlam, hphi, ht0b, ht5b, p11663_1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          rcases p11663_3 (m.d 0 2) (by simp) with h11667 | h11667
          · rcases p11663_3 (m.d 1 2) (by simp) with h11668 | h11668
            · rcases p11663_3 (m.d 2 3) (by simp) with h11669 | h11669
              · linarith only [h11648, h11669, hlam]
              · linarith only [h11659, h11669, hlam]
            · linarith only [h0, h11668, hlam, p11663_1]
          · linarith only [h11667, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          rcases p11663_3 (m.d 0 2) (by simp) with h11674 | h11674
          · rcases p11663_3 (m.d 1 2) (by simp) with h11675 | h11675
            · rcases p11663_3 (m.d 2 3) (by simp) with h11676 | h11676
              · linarith only [h11648, h11676, hlam]
              · linarith only [h11660, h11676, hlam]
            · linarith only [h11655, h11675, hlam]
          · linarith only [h11674, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p11663_1, u0ehi1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11659, h11662, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11663_1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          rcases p11663_3 (m.d 0 2) (by simp) with h11684 | h11684
          · linarith only [h0, h11684, hlam]
          · linarith only [h11649, h11684, hlam]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          rcases p11663_3 (m.d 0 2) (by simp) with h11687 | h11687
          · linarith only [h0, h11687, hlam]
          · linarith only [h11650, h11687, hlam]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11648, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11654, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11648, h11659, h11662, hc02, hc45, hlam, hphi, ht0b, ht5b, p11663_1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          rcases p11663_3 (m.d 0 2) (by simp) with h11694 | h11694
          · rcases p11663_3 (m.d 1 2) (by simp) with h11695 | h11695
            · rcases p11663_3 (m.d 2 3) (by simp) with h11696 | h11696
              · rcases p11663_3 (m.d 2 4) (by simp) with h11697 | h11697
                · linarith only [h11659, h11697, hlam]
                · linarith only [h11661, h11697, hlam]
              · linarith only [h11660, h11696, hlam]
            · linarith only [h11655, h11695, hlam]
          · linarith only [h11650, h11694, hlam]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11649, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h0, hc24, hlam, hphi, ht01, ht12, p11663_1, u0ehi1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11659, hlam, p11663_1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          rcases p11663_3 (m.d 0 2) (by simp) with h11707 | h11707
          · rcases p11663_3 (m.d 1 2) (by simp) with h11708 | h11708
            · rcases p11663_3 (m.d 2 3) (by simp) with h11709 | h11709
              · rcases p11663_3 (m.d 2 4) (by simp) with h11710 | h11710
                · rcases p11663_3 (m.d 2 5) (by simp) with h11711 | h11711
                  · linarith only [h11661, h11711, hlam]
                  · rcases h3bigk with h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c | h11713c
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h8410, hlam, p11713_1]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11659, h11660, h11662, hc03, hc45, hlam, hphi, ht0b, ht5b, p11663_1, p11713_1]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      rcases p11713_3 (m.d 0 3) (by simp) with h11717 | h11717
                      · rcases p11713_3 (m.d 1 3) (by simp) with h11718 | h11718
                        · rcases p11713_3 (m.d 2 3) (by simp) with h11719 | h11719
                          · linarith only [h11648, h11719, hlam]
                          · linarith only [h11659, h11719, hlam]
                        · linarith only [h11656, h11718, hlam]
                      · linarith only [h11717, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      rcases p11713_3 (m.d 0 3) (by simp) with h11724 | h11724
                      · rcases p11713_3 (m.d 1 3) (by simp) with h11725 | h11725
                        · rcases p11713_3 (m.d 2 3) (by simp) with h11726 | h11726
                          · linarith only [h11648, h11726, hlam]
                          · linarith only [h11660, h11726, hlam]
                        · linarith only [h11657, h11725, hlam]
                      · linarith only [h11724, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11654, hc12, hlam, hphi, ht01, p11713_1, u0ehi2]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11654, h11659, h11660, h11662, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11663_1, p11713_1]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      rcases p11713_3 (m.d 0 3) (by simp) with h11734 | h11734
                      · linarith only [h11734, h8410, hlam]
                      · linarith only [h11651, h11734, hlam]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      rcases p11713_3 (m.d 0 3) (by simp) with h11737 | h11737
                      · linarith only [h11737, h8410, hlam]
                      · linarith only [h11652, h11737, hlam]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11648, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11654, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h0, h11648, h11662, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11713_1]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      rcases p11713_3 (m.d 0 3) (by simp) with h11744 | h11744
                      · rcases p11713_3 (m.d 1 3) (by simp) with h11745 | h11745
                        · rcases p11713_3 (m.d 2 3) (by simp) with h11746 | h11746
                          · rcases p11713_3 (m.d 3 4) (by simp) with h11747 | h11747
                            · linarith only [h11659, h11747, hlam]
                            · linarith only [h11662, h11747, hlam]
                          · linarith only [h11746, hlam, p11713_0]
                        · linarith only [h11657, h11745, hlam]
                      · linarith only [h11652, h11744, hlam]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11651, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11656, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11659, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h0, h11648, h11659, h11662, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11713_1]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11652, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11657, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11660, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [h11662, hlam, p11713_0]
                    · have p11713_0 := h11713c.1
                      have p11713_1 := h11713c.2.1
                      have p11713_2 := h11713c.2.2.1
                      have p11713_3 := h11713c.2.2.2
                      linarith only [hlam, p11713_0]
                · linarith only [h11661, h11710, hlam]
              · linarith only [h11660, h11709, hlam]
            · linarith only [h11655, h11708, hlam]
          · linarith only [h11650, h11707, hlam]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11650, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11655, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11660, hlam, p11663_1]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [h11661, hlam, p11663_0]
        · have p11663_0 := h11663c.1
          have p11663_1 := h11663c.2.1
          have p11663_2 := h11663c.2.2.1
          have p11663_3 := h11663c.2.2.2
          linarith only [hlam, p11663_0]
      · rcases h2bigk with h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h0, hlam, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h0, h11659, h11661, h11662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h0, h11661, h11662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          rcases p11772_3 (m.d 0 2) (by simp) with h11777 | h11777
          · rcases p11772_3 (m.d 1 2) (by simp) with h11778 | h11778
            · rcases p11772_3 (m.d 2 3) (by simp) with h11779 | h11779
              · linarith only [h11648, h11779, hlam]
              · linarith only [h11660, h11779, hlam]
            · linarith only [h11655, h11778, hlam]
          · linarith only [h11777, hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p11772_1, u0ehi1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11659, h11661, h11662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11661, h11662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          rcases p11772_3 (m.d 0 2) (by simp) with h11788 | h11788
          · linarith only [h0, h11788, hlam]
          · linarith only [h11650, h11788, hlam]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11648, hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11654, hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11648, h11661, h11662, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h0, h11648, h11661, h11662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11649, hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h0, hc24, hlam, hphi, ht01, ht12, p11772_1, u0ehi1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11659, hlam, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11648, h11659, h11661, h11662, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11650, hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11655, hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11660, hlam, p11772_1]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [h11661, hlam, p11772_0]
        · have p11772_0 := h11772c.1
          have p11772_1 := h11772c.2.1
          have p11772_2 := h11772c.2.2.1
          have p11772_3 := h11772c.2.2.2
          linarith only [hlam, p11772_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h11806 | h11806
      · linarith only [h11659, h11661, h11806, hlam]
      · rcases h2bigk with h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c | h11808c
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h0, hlam, p11808_1]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11811 | h11811
          · rcases p11808_3 (m.d 1 2) (by simp) with h11812 | h11812
            · rcases p11808_3 (m.d 2 3) (by simp) with h11813 | h11813
              · linarith only [h11813, hlam, p11808_0]
              · rcases p11808_3 (m.d 2 4) (by simp) with h11815 | h11815
                · linarith only [h11649, h11815, hlam]
                · rcases p11808_3 (m.d 2 5) (by simp) with h11817 | h11817
                  · linarith only [h11650, h11817, hlam]
                  · rcases h3bigk with h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c | h11819c
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h8410, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 3) (by simp) with h11822 | h11822
                      · rcases p11819_3 (m.d 1 3) (by simp) with h11823 | h11823
                        · rcases p11819_3 (m.d 2 3) (by simp) with h11824 | h11824
                          · linarith only [h11648, h11824, hlam]
                          · rcases p11819_3 (m.d 3 4) (by simp) with h11826 | h11826
                            · linarith only [h11651, h11826, hlam]
                            · rcases p11819_3 (m.d 3 5) (by simp) with h11828 | h11828
                              · linarith only [h11652, h11828, hlam]
                              · rcases h5bigk with h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h10008, hlam, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  rcases p11830_3 (m.d 0 5) (by simp) with h11833 | h11833
                                  · rcases p11830_3 (m.d 1 5) (by simp) with h11834 | h11834
                                    · rcases p11830_3 (m.d 2 5) (by simp) with h11835 | h11835
                                      · linarith only [h11650, h11835, hlam]
                                      · rcases p11830_3 (m.d 3 5) (by simp) with h11837 | h11837
                                        · linarith only [h11652, h11837, hlam]
                                        · rcases p11830_3 (m.d 4 5) (by simp) with h11839 | h11839
                                          · linarith only [h11653, h11839, hlam]
                                          · linarith only [h11661, h11839, hlam]
                                    · linarith only [h11655, h11834, hlam]
                                  · linarith only [h11650, h11833, hlam]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  rcases p11830_3 (m.d 0 5) (by simp) with h11844 | h11844
                                  · rcases p11830_3 (m.d 1 5) (by simp) with h11845 | h11845
                                    · rcases p11830_3 (m.d 2 5) (by simp) with h11846 | h11846
                                      · linarith only [h11650, h11846, hlam]
                                      · linarith only [h11660, h11846, hlam]
                                    · linarith only [h11657, h11845, hlam]
                                  · linarith only [h11652, h11844, hlam]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h0, h11648, h11651, h11653, h11659, h11661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11656, h11658, hc13, hlam, hphi, ht01, p11830_1, u0ehi4]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  rcases p11830_3 (m.d 0 5) (by simp) with h11854 | h11854
                                  · linarith only [h10008, h11854, hlam]
                                  · linarith only [h11650, h11854, hlam]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  rcases p11830_3 (m.d 0 5) (by simp) with h11857 | h11857
                                  · linarith only [h10008, h11857, hlam]
                                  · linarith only [h11652, h11857, hlam]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11654, h11656, h11658, h11659, h11661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11650, hlam, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11655, hlam, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h0, h11650, h11806, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11661, hlam, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11652, hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11657, hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11660, hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11806, hlam, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11653, hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11658, hlam, p11830_0]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h0, h11648, h11651, h11653, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [h11806, hc34, hc45, hlam, hphi, p11830_1]
                                · have p11830_0 := h11830c.1
                                  have p11830_1 := h11830c.2.1
                                  have p11830_2 := h11830c.2.2.1
                                  have p11830_3 := h11830c.2.2.2
                                  linarith only [hlam, p11830_0]
                        · linarith only [h11654, h11823, hlam]
                      · linarith only [h11648, h11822, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 3) (by simp) with h11878 | h11878
                      · rcases p11819_3 (m.d 1 3) (by simp) with h11879 | h11879
                        · rcases p11819_3 (m.d 2 3) (by simp) with h11880 | h11880
                          · linarith only [h11648, h11880, hlam]
                          · linarith only [h11659, h11880, hlam]
                        · linarith only [h11656, h11879, hlam]
                      · linarith only [h11878, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 3) (by simp) with h11885 | h11885
                      · rcases p11819_3 (m.d 1 3) (by simp) with h11886 | h11886
                        · rcases p11819_3 (m.d 2 3) (by simp) with h11887 | h11887
                          · linarith only [h11648, h11887, hlam]
                          · linarith only [h11660, h11887, hlam]
                        · linarith only [h11657, h11886, hlam]
                      · linarith only [h11885, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11654, hc12, hlam, hphi, ht01, p11819_1, u0ehi2]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 3) (by simp) with h11894 | h11894
                      · linarith only [h11894, h8410, hlam]
                      · linarith only [h11648, h11894, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 3) (by simp) with h11897 | h11897
                      · linarith only [h11897, h8410, hlam]
                      · linarith only [h11651, h11897, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      rcases p11819_3 (m.d 0 3) (by simp) with h11900 | h11900
                      · linarith only [h11900, h8410, hlam]
                      · linarith only [h11652, h11900, hlam]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11648, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11654, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h0, h11806, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11651, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11656, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11659, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11806, hlam, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11652, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11657, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h11660, hlam, p11819_0]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [h0, h11660, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p11819_1]
                    · have p11819_0 := h11819c.1
                      have p11819_1 := h11819c.2.1
                      have p11819_2 := h11819c.2.2.1
                      have p11819_3 := h11819c.2.2.2
                      linarith only [hlam, p11819_0]
            · linarith only [h11654, h11812, hlam]
          · linarith only [h11811, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11920 | h11920
          · rcases p11808_3 (m.d 1 2) (by simp) with h11921 | h11921
            · rcases p11808_3 (m.d 2 3) (by simp) with h11922 | h11922
              · linarith only [h11648, h11922, hlam]
              · linarith only [h11659, h11922, hlam]
            · linarith only [h0, h11651, h11653, h11661, h11921, hc03, hlam, hphi, u0ehi1]
          · linarith only [h11920, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11927 | h11927
          · rcases p11808_3 (m.d 1 2) (by simp) with h11928 | h11928
            · rcases p11808_3 (m.d 2 3) (by simp) with h11929 | h11929
              · linarith only [h11648, h11929, hlam]
              · linarith only [h11660, h11929, hlam]
            · linarith only [h11655, h11928, hlam]
          · linarith only [h11927, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11648, h11651, h11653, h11661, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11936 | h11936
          · linarith only [h0, h11936, hlam]
          · linarith only [h11648, h11936, hlam]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11939 | h11939
          · linarith only [h0, h11939, hlam]
          · linarith only [h11649, h11939, hlam]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11942 | h11942
          · linarith only [h0, h11942, hlam]
          · linarith only [h11650, h11942, hlam]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11648, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11654, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11948 | h11948
          · rcases p11808_3 (m.d 1 2) (by simp) with h11949 | h11949
            · rcases p11808_3 (m.d 2 3) (by simp) with h11950 | h11950
              · rcases p11808_3 (m.d 2 4) (by simp) with h11951 | h11951
                · linarith only [h11659, h11951, hlam]
                · rcases p11808_3 (m.d 2 5) (by simp) with h11953 | h11953
                  · linarith only [h11660, h11953, hlam]
                  · linarith only [h11661, h11953, hlam]
              · linarith only [h11659, h11950, hlam]
            · linarith only [h10008, h11648, h11654, h11656, h11658, h11949, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11808_1]
          · linarith only [h11649, h11948, hlam]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h11959 | h11959
          · rcases p11808_3 (m.d 1 2) (by simp) with h11960 | h11960
            · rcases p11808_3 (m.d 2 3) (by simp) with h11961 | h11961
              · rcases p11808_3 (m.d 2 4) (by simp) with h11962 | h11962
                · linarith only [h11659, h11962, hlam]
                · rcases p11808_3 (m.d 2 5) (by simp) with h11964 | h11964
                  · linarith only [h11660, h11964, hlam]
                  · rcases h3bigk with h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c | h11966c
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h8410, hlam, p11966_1]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h0, h11648, h11659, h11661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p11966_1]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      rcases p11966_3 (m.d 0 3) (by simp) with h11970 | h11970
                      · rcases p11966_3 (m.d 1 3) (by simp) with h11971 | h11971
                        · rcases p11966_3 (m.d 2 3) (by simp) with h11972 | h11972
                          · linarith only [h11648, h11972, hlam]
                          · linarith only [h11659, h11972, hlam]
                        · linarith only [h11656, h11971, hlam]
                      · linarith only [h11970, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      rcases p11966_3 (m.d 0 3) (by simp) with h11977 | h11977
                      · rcases p11966_3 (m.d 1 3) (by simp) with h11978 | h11978
                        · rcases p11966_3 (m.d 2 3) (by simp) with h11979 | h11979
                          · linarith only [h11648, h11979, hlam]
                          · linarith only [h11660, h11979, hlam]
                        · linarith only [h11657, h11978, hlam]
                      · linarith only [h11977, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [hc13, hlam, hphi, ht01, p11966_1, u0ehi2]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11654, h11661, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p11966_1]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      rcases p11966_3 (m.d 0 3) (by simp) with h11987 | h11987
                      · linarith only [h11987, h8410, hlam]
                      · linarith only [h11651, h11987, hlam]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      rcases p11966_3 (m.d 0 3) (by simp) with h11990 | h11990
                      · linarith only [h11990, h8410, hlam]
                      · linarith only [h11652, h11990, hlam]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11648, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11654, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      rcases p11966_3 (m.d 0 3) (by simp) with h11996 | h11996
                      · rcases p11966_3 (m.d 1 3) (by simp) with h11997 | h11997
                        · rcases p11966_3 (m.d 2 3) (by simp) with h11998 | h11998
                          · rcases p11966_3 (m.d 3 4) (by simp) with h11999 | h11999
                            · linarith only [h11999, hlam, p11966_0]
                            · rcases p11966_3 (m.d 3 5) (by simp) with h12001 | h12001
                              · linarith only [h11660, h12001, hlam]
                              · linarith only [h11806, h12001, hlam]
                          · linarith only [h11998, hlam, p11966_0]
                        · linarith only [h11656, h11997, hlam]
                      · linarith only [h11651, h11996, hlam]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      rcases p11966_3 (m.d 0 3) (by simp) with h12007 | h12007
                      · rcases p11966_3 (m.d 1 3) (by simp) with h12008 | h12008
                        · rcases p11966_3 (m.d 2 3) (by simp) with h12009 | h12009
                          · rcases p11966_3 (m.d 3 4) (by simp) with h12010 | h12010
                            · linarith only [h11659, h12010, hlam]
                            · rcases p11966_3 (m.d 3 5) (by simp) with h12012 | h12012
                              · linarith only [h12012, hlam, p11966_0]
                              · rcases h5bigk with h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h10008, hlam, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  rcases p12014_3 (m.d 0 5) (by simp) with h12017 | h12017
                                  · rcases p12014_3 (m.d 1 5) (by simp) with h12018 | h12018
                                    · rcases p12014_3 (m.d 2 5) (by simp) with h12019 | h12019
                                      · linarith only [h11650, h12019, hlam]
                                      · rcases p12014_3 (m.d 3 5) (by simp) with h12021 | h12021
                                        · linarith only [h11652, h12021, hlam]
                                        · rcases p12014_3 (m.d 4 5) (by simp) with h12023 | h12023
                                          · linarith only [h11653, h12023, hlam]
                                          · linarith only [h11661, h12023, hlam]
                                    · linarith only [h11655, h12018, hlam]
                                  · linarith only [h11650, h12017, hlam]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  rcases p12014_3 (m.d 0 5) (by simp) with h12028 | h12028
                                  · rcases p12014_3 (m.d 1 5) (by simp) with h12029 | h12029
                                    · rcases p12014_3 (m.d 2 5) (by simp) with h12030 | h12030
                                      · linarith only [h11650, h12030, hlam]
                                      · linarith only [h11660, h12030, hlam]
                                    · linarith only [h11657, h12029, hlam]
                                  · linarith only [h11652, h12028, hlam]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11651, h11653, h11659, h11661, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11656, h11658, hc13, hlam, hphi, ht01, p12014_1, u0ehi4]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  rcases p12014_3 (m.d 0 5) (by simp) with h12038 | h12038
                                  · linarith only [h10008, h12038, hlam]
                                  · linarith only [h11650, h12038, hlam]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  rcases p12014_3 (m.d 0 5) (by simp) with h12041 | h12041
                                  · linarith only [h10008, h12041, hlam]
                                  · linarith only [h11652, h12041, hlam]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11654, h11656, h11658, h11659, h11661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11650, hlam, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11655, hlam, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p11808_1, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11661, hlam, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11652, hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11657, hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11660, hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11806, hlam, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11653, hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h11658, hlam, p12014_0]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h0, h11648, h11651, h11653, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [h0, h11648, h11651, h11653, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p12014_1]
                                · have p12014_0 := h12014c.1
                                  have p12014_1 := h12014c.2.1
                                  have p12014_2 := h12014c.2.2.1
                                  have p12014_3 := h12014c.2.2.2
                                  linarith only [hlam, p12014_0]
                          · linarith only [h12009, hlam, p11966_0]
                        · linarith only [h11657, h12008, hlam]
                      · linarith only [h11652, h12007, hlam]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11651, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11656, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11659, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11806, hlam, p11966_1]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11652, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11657, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h11660, hlam, p11966_0]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [h0, h11648, h11660, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11966_1]
                    · have p11966_0 := h11966c.1
                      have p11966_1 := h11966c.2.1
                      have p11966_2 := h11966c.2.2.1
                      have p11966_3 := h11966c.2.2.2
                      linarith only [hlam, p11966_0]
              · linarith only [h11660, h11961, hlam]
            · linarith only [h11655, h11960, hlam]
          · linarith only [h11650, h11959, hlam]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11649, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h0, h11661, hc25, hlam, hphi, ht01, ht12, p11808_1, u0ehi1]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11659, hlam, p11808_1]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11661, hlam, p11808_1]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11650, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11655, hlam, p11808_0]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [h11660, hlam, p11808_1]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          rcases p11808_3 (m.d 0 2) (by simp) with h12084 | h12084
          · rcases p11808_3 (m.d 1 2) (by simp) with h12085 | h12085
            · rcases p11808_3 (m.d 2 3) (by simp) with h12086 | h12086
              · rcases p11808_3 (m.d 2 4) (by simp) with h12087 | h12087
                · linarith only [h11661, h12087, hlam]
                · rcases p11808_3 (m.d 2 5) (by simp) with h12089 | h12089
                  · rcases h3bigk with h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c | h12090c
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h8410, hlam, p12090_1]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11648, h11659, h11660, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11808_1, p12090_1]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11651, h11653, h11659, h11661, hlam, p11808_1, p12090_2]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      rcases p12090_3 (m.d 0 3) (by simp) with h12095 | h12095
                      · rcases p12090_3 (m.d 1 3) (by simp) with h12096 | h12096
                        · rcases p12090_3 (m.d 2 3) (by simp) with h12097 | h12097
                          · linarith only [h11648, h12097, hlam]
                          · linarith only [h11660, h12097, hlam]
                        · linarith only [h11657, h12096, hlam]
                      · linarith only [h12095, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11651, h11653, h11654, h11659, h11661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p12090_1]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11654, h11659, h11660, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p12090_1]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11651, h11653, h11659, h11661, h8410, hlam, p11808_1, p12090_2]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      rcases p12090_3 (m.d 0 3) (by simp) with h12106 | h12106
                      · linarith only [h12106, h8410, hlam]
                      · linarith only [h11652, h12106, hlam]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11648, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11654, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      rcases p12090_3 (m.d 0 3) (by simp) with h12112 | h12112
                      · rcases p12090_3 (m.d 1 3) (by simp) with h12113 | h12113
                        · rcases p12090_3 (m.d 2 3) (by simp) with h12114 | h12114
                          · rcases p12090_3 (m.d 3 4) (by simp) with h12115 | h12115
                            · linarith only [h12115, hlam, p12090_0]
                            · rcases p12090_3 (m.d 3 5) (by simp) with h12117 | h12117
                              · linarith only [h11660, h12117, hlam]
                              · linarith only [h11806, h12117, hlam]
                          · linarith only [h12114, hlam, p12090_0]
                        · linarith only [h11656, h12113, hlam]
                      · linarith only [h11651, h12112, hlam]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      rcases p12090_3 (m.d 0 3) (by simp) with h12123 | h12123
                      · rcases p12090_3 (m.d 1 3) (by simp) with h12124 | h12124
                        · rcases p12090_3 (m.d 2 3) (by simp) with h12125 | h12125
                          · rcases p12090_3 (m.d 3 4) (by simp) with h12126 | h12126
                            · linarith only [h11659, h12126, hlam]
                            · rcases p12090_3 (m.d 3 5) (by simp) with h12128 | h12128
                              · linarith only [h12128, hlam, p12090_0]
                              · rcases h5bigk with h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c | h12130c
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h10008, hlam, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11651, h11653, h11659, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11808_1, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  rcases p12130_3 (m.d 0 5) (by simp) with h12134 | h12134
                                  · rcases p12130_3 (m.d 1 5) (by simp) with h12135 | h12135
                                    · rcases p12130_3 (m.d 2 5) (by simp) with h12136 | h12136
                                      · linarith only [h11650, h12136, hlam]
                                      · linarith only [h11660, h12136, hlam]
                                    · linarith only [h11657, h12135, hlam]
                                  · linarith only [h11652, h12134, hlam]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h0, h11648, h11651, h11653, h11659, h11661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11654, h11656, h11658, hc12, hlam, hphi, ht01, p12130_1, u0ehi4]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11654, h11656, h11658, h11659, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  rcases p12130_3 (m.d 0 5) (by simp) with h12145 | h12145
                                  · linarith only [h10008, h12145, hlam]
                                  · linarith only [h11652, h12145, hlam]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11654, h11656, h11658, h11659, h11661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11808_1, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11650, hlam, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11655, hlam, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h0, h11648, h11660, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11661, hlam, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11652, hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11657, hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11660, hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11806, hlam, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11653, hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h11658, hlam, p12130_0]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h0, h11648, h11651, h11653, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [h0, h11648, h11651, h11653, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p12130_1]
                                · have p12130_0 := h12130c.1
                                  have p12130_1 := h12130c.2.1
                                  have p12130_2 := h12130c.2.2.1
                                  have p12130_3 := h12130c.2.2.2
                                  linarith only [hlam, p12130_0]
                          · linarith only [h12125, hlam, p12090_0]
                        · linarith only [h11657, h12124, hlam]
                      · linarith only [h11652, h12123, hlam]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11651, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11656, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11659, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11806, hlam, p12090_1]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11652, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11657, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h11660, hlam, p12090_0]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [h0, h11648, h11660, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12090_1]
                    · have p12090_0 := h12090c.1
                      have p12090_1 := h12090c.2.1
                      have p12090_2 := h12090c.2.2.1
                      have p12090_3 := h12090c.2.2.2
                      linarith only [hlam, p12090_0]
                  · linarith only [h11661, h12089, hlam]
              · linarith only [h11659, h12086, hlam]
            · linarith only [h0, h11648, h11651, h11653, h11661, h12085, hlam, p11808_1]
          · linarith only [h11649, h12084, hlam]
        · have p11808_0 := h11808c.1
          have p11808_1 := h11808c.2.1
          have p11808_2 := h11808c.2.2.1
          have p11808_3 := h11808c.2.2.2
          linarith only [hlam, p11808_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h12182 | h12182
    · linarith only [h11659, h11660, h12182, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h12184 | h12184
      · linarith only [h0, h11648, h11652, h11659, h11660, h12182, h12184, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h2bigk with h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c | h12186c
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h0, hlam, p12186_1]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          rcases p12186_3 (m.d 0 2) (by simp) with h12189 | h12189
          · rcases p12186_3 (m.d 1 2) (by simp) with h12190 | h12190
            · rcases p12186_3 (m.d 2 3) (by simp) with h12191 | h12191
              · linarith only [h12191, hlam, p12186_0]
              · rcases p12186_3 (m.d 2 4) (by simp) with h12193 | h12193
                · linarith only [h11649, h12193, hlam]
                · rcases p12186_3 (m.d 2 5) (by simp) with h12195 | h12195
                  · linarith only [h11650, h12195, hlam]
                  · linarith only [h11660, h12195, hlam]
            · linarith only [h11654, h12190, hlam]
          · linarith only [h12189, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          rcases p12186_3 (m.d 0 2) (by simp) with h12200 | h12200
          · rcases p12186_3 (m.d 1 2) (by simp) with h12201 | h12201
            · rcases p12186_3 (m.d 2 3) (by simp) with h12202 | h12202
              · linarith only [h11648, h12202, hlam]
              · linarith only [h11659, h12202, hlam]
            · linarith only [h0, h12201, hlam, p12186_1]
          · linarith only [h12200, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          rcases p12186_3 (m.d 0 2) (by simp) with h12207 | h12207
          · rcases p12186_3 (m.d 1 2) (by simp) with h12208 | h12208
            · rcases p12186_3 (m.d 2 3) (by simp) with h12209 | h12209
              · linarith only [h11648, h12209, hlam]
              · rcases p12186_3 (m.d 2 4) (by simp) with h12211 | h12211
                · linarith only [h11649, h12211, hlam]
                · rcases p12186_3 (m.d 2 5) (by simp) with h12213 | h12213
                  · linarith only [h12213, hlam, p12186_0]
                  · rcases h3bigk with h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c | h12215c
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h8410, hlam, p12215_1]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      rcases p12215_3 (m.d 0 3) (by simp) with h12218 | h12218
                      · rcases p12215_3 (m.d 1 3) (by simp) with h12219 | h12219
                        · rcases p12215_3 (m.d 2 3) (by simp) with h12220 | h12220
                          · linarith only [h11648, h12220, hlam]
                          · rcases p12215_3 (m.d 3 4) (by simp) with h12222 | h12222
                            · linarith only [h11651, h12222, hlam]
                            · rcases p12215_3 (m.d 3 5) (by simp) with h12224 | h12224
                              · linarith only [h11652, h12224, hlam]
                              · linarith only [h11660, h12224, hlam]
                        · linarith only [h11654, h12219, hlam]
                      · linarith only [h11648, h12218, hlam]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11651, h11653, h11659, h11660, h12184, hlam, p12215_2]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h0, h11648, h11659, h11660, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12215_1]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11654, hc12, hlam, hphi, ht01, p12215_1, u0ehi2]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      rcases p12215_3 (m.d 0 3) (by simp) with h12233 | h12233
                      · linarith only [h12233, h8410, hlam]
                      · linarith only [h11648, h12233, hlam]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11651, h11653, h11659, h11660, h12184, h8410, hlam, p12215_2]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11659, h11660, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12215_1]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11648, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11654, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11651, h11653, h11660, h12184, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12215_1]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11660, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11651, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11656, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11659, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h12184, hlam, p12215_1]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11652, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h11657, hlam, p12215_0]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [h0, h11648, h11651, h11653, h11659, h12184, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12215_1]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      rcases p12215_3 (m.d 0 3) (by simp) with h12251 | h12251
                      · rcases p12215_3 (m.d 1 3) (by simp) with h12252 | h12252
                        · rcases p12215_3 (m.d 2 3) (by simp) with h12253 | h12253
                          · linarith only [h11660, h12253, hlam]
                          · linarith only [h11659, h12253, hlam]
                        · linarith only [h11656, h12252, hlam]
                      · linarith only [h11651, h12251, hlam]
                    · have p12215_0 := h12215c.1
                      have p12215_1 := h12215c.2.1
                      have p12215_2 := h12215c.2.2.1
                      have p12215_3 := h12215c.2.2.2
                      linarith only [hlam, p12215_0]
            · linarith only [h11655, h12208, hlam]
          · linarith only [h12207, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p12186_1, u0ehi1]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          rcases p12186_3 (m.d 0 2) (by simp) with h12263 | h12263
          · linarith only [h0, h12263, hlam]
          · linarith only [h11648, h12263, hlam]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          rcases p12186_3 (m.d 0 2) (by simp) with h12266 | h12266
          · linarith only [h0, h12266, hlam]
          · linarith only [h11649, h12266, hlam]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          rcases p12186_3 (m.d 0 2) (by simp) with h12269 | h12269
          · linarith only [h0, h12269, hlam]
          · linarith only [h11650, h12269, hlam]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11648, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11654, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11648, h11651, h11653, h11660, h12184, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p12186_1]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11660, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11649, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h0, h11648, h11651, h11653, h11660, h12184, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12186_1]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11659, hlam, p12186_1]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h12182, hlam, p12186_1]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11650, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11655, hlam, p12186_0]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [h11650, h11659, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p12186_1]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          rcases p12186_3 (m.d 0 2) (by simp) with h12285 | h12285
          · rcases p12186_3 (m.d 1 2) (by simp) with h12286 | h12286
            · rcases p12186_3 (m.d 2 3) (by simp) with h12287 | h12287
              · linarith only [h11660, h12287, hlam]
              · linarith only [h11659, h12287, hlam]
            · linarith only [h0, h11651, h11653, h11660, h12184, h12286, hc03, hlam, hphi, p12186_1, u0ehi1]
          · linarith only [h11649, h12285, hlam]
        · have p12186_0 := h12186c.1
          have p12186_1 := h12186c.2.1
          have p12186_2 := h12186c.2.2.1
          have p12186_3 := h12186c.2.2.2
          linarith only [hlam, p12186_0]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11652 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11653 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11654 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11655 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11656 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11657 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11658 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h11659 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h12293 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 4 5 (by decide) (by decide) with h12294 | h12294
  · rcases m.htr 3 4 5 (by decide) (by decide) with h12295 | h12295
    · rcases h2bigk with h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c | h12296c
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h0, hlam, p12296_1]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        rcases p12296_3 (m.d 0 2) (by simp) with h12299 | h12299
        · rcases p12296_3 (m.d 1 2) (by simp) with h12300 | h12300
          · rcases p12296_3 (m.d 2 3) (by simp) with h12301 | h12301
            · linarith only [h12301, hlam, p12296_0]
            · rcases p12296_3 (m.d 2 4) (by simp) with h12303 | h12303
              · linarith only [h11649, h12303, hlam]
              · linarith only [h11659, h12303, hlam]
          · linarith only [h11654, h12300, hlam]
        · linarith only [h12299, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        rcases p12296_3 (m.d 0 2) (by simp) with h12308 | h12308
        · rcases p12296_3 (m.d 1 2) (by simp) with h12309 | h12309
          · rcases p12296_3 (m.d 2 3) (by simp) with h12310 | h12310
            · linarith only [h11648, h12310, hlam]
            · rcases p12296_3 (m.d 2 4) (by simp) with h12312 | h12312
              · linarith only [h12312, hlam, p12296_0]
              · rcases p12296_3 (m.d 2 5) (by simp) with h12314 | h12314
                · linarith only [h11650, h12314, hlam]
                · rcases h3bigk with h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c | h12316c
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h8410, hlam, p12316_1]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    rcases p12316_3 (m.d 0 3) (by simp) with h12319 | h12319
                    · rcases p12316_3 (m.d 1 3) (by simp) with h12320 | h12320
                      · rcases p12316_3 (m.d 2 3) (by simp) with h12321 | h12321
                        · linarith only [h11648, h12321, hlam]
                        · rcases p12316_3 (m.d 3 4) (by simp) with h12323 | h12323
                          · linarith only [h11651, h12323, hlam]
                          · linarith only [h11659, h12323, hlam]
                      · linarith only [h11654, h12320, hlam]
                    · linarith only [h11648, h12319, hlam]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11648, h11659, h12293, h12295, hc02, hc45, hlam, hphi, ht0b, ht5b, p12316_1]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11651, h11659, h12293, hlam, p12316_2]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11654, hc12, hlam, hphi, ht01, p12316_1, u0ehi2]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    rcases p12316_3 (m.d 0 3) (by simp) with h12332 | h12332
                    · linarith only [h12332, h8410, hlam]
                    · linarith only [h11648, h12332, hlam]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11654, h11659, h12293, h12295, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12316_1]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11651, h11659, h12293, h8410, hlam, p12316_2]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11648, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11654, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11659, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11651, h11659, hc03, hc35, hlam, hphi, ht0b, ht5b, p12316_1]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11651, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11656, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h0, h11648, h11651, h12293, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p12316_1]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    rcases p12316_3 (m.d 0 3) (by simp) with h12346 | h12346
                    · rcases p12316_3 (m.d 1 3) (by simp) with h12347 | h12347
                      · rcases p12316_3 (m.d 2 3) (by simp) with h12348 | h12348
                        · linarith only [h11659, h12348, hlam]
                        · linarith only [h12293, h12348, hlam]
                      · linarith only [h11657, h12347, hlam]
                    · linarith only [h11652, h12346, hlam]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11652, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h11657, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h12293, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [h12295, hlam, p12316_0]
                  · have p12316_0 := h12316c.1
                    have p12316_1 := h12316c.2.1
                    have p12316_2 := h12316c.2.2.1
                    have p12316_3 := h12316c.2.2.2
                    linarith only [hlam, p12316_0]
          · linarith only [h0, h12309, hlam, p12296_1]
        · linarith only [h12308, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        rcases p12296_3 (m.d 0 2) (by simp) with h12360 | h12360
        · rcases p12296_3 (m.d 1 2) (by simp) with h12361 | h12361
          · rcases p12296_3 (m.d 2 3) (by simp) with h12362 | h12362
            · linarith only [h11648, h12362, hlam]
            · linarith only [h12293, h12362, hlam]
          · linarith only [h11655, h12361, hlam]
        · linarith only [h12360, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [hc12, hlam, hphi, ht01, p12296_1, u0ehi1]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        rcases p12296_3 (m.d 0 2) (by simp) with h12369 | h12369
        · linarith only [h0, h12369, hlam]
        · linarith only [h11648, h12369, hlam]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        rcases p12296_3 (m.d 0 2) (by simp) with h12372 | h12372
        · linarith only [h0, h12372, hlam]
        · linarith only [h11649, h12372, hlam]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        rcases p12296_3 (m.d 0 2) (by simp) with h12375 | h12375
        · linarith only [h0, h12375, hlam]
        · linarith only [h11650, h12375, hlam]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h11648, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h11654, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h11659, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h11648, h11651, h11659, hc02, hc25, hlam, hphi, ht0b, ht5b, p12296_1]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h11649, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h0, h11648, h11651, h11659, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12296_1]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h0, h11648, h11651, h11659, h12293, h12295, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12296_1]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        rcases p12296_3 (m.d 0 2) (by simp) with h12387 | h12387
        · rcases p12296_3 (m.d 1 2) (by simp) with h12388 | h12388
          · rcases p12296_3 (m.d 2 3) (by simp) with h12389 | h12389
            · linarith only [h11659, h12389, hlam]
            · linarith only [h12293, h12389, hlam]
          · linarith only [h11655, h12388, hlam]
        · linarith only [h11650, h12387, hlam]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h11650, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h11655, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h12293, hlam, p12296_1]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [h12294, hlam, p12296_0]
      · have p12296_0 := h12296c.1
        have p12296_1 := h12296c.2.1
        have p12296_2 := h12296c.2.2.1
        have p12296_3 := h12296c.2.2.2
        linarith only [hlam, p12296_0]
    · linarith only [h11653, h11659, h12293, h12295, hc04, hc35, hlam, hphi, ht0b, ht5b]
  · linarith only [h11659, h12293, h12294, hlam]

end R2N4
