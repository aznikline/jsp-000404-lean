import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_68S10

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h709 | h709
  · rcases m.htr 0 3 4 (by decide) (by decide) with h710 | h710
    · rcases m.htr 0 3 5 (by decide) (by decide) with h711 | h711
      · rcases m.htr 0 4 5 (by decide) (by decide) with h712 | h712
        · rcases m.htr 1 2 3 (by decide) (by decide) with h713 | h713
          · linarith only [h0, h4, h709, h713, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h715 | h715
            · rcases m.htr 1 3 4 (by decide) (by decide) with h716 | h716
              · rcases m.htr 1 4 5 (by decide) (by decide) with h717 | h717
                · rcases h0bigk with h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, h709, h712, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h711, hc01, hc35, hlam, hphi, ht0b, ht5b, p718_1]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, h712, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h0, hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h4, hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, h712, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h1, hlam, p718_1]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h0, h715, h717, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, h4, h712, hc23, hlam, hphi, ht12, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, h4, hc23, hlam, hphi, ht12, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h2, hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h709, hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h710, hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h3, hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h0, h715, h717, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p718_1, u1ehi4]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h711, hlam, p718_0]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [h712, hlam, p718_1]
                  · have p718_0 := h718c.1
                    have p718_1 := h718c.2.1
                    have p718_2 := h718c.2.2.1
                    have p718_3 := h718c.2.2.2
                    linarith only [hlam, p718_0]
                · linarith only [h4, h709, h712, h717, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h4, h710, h713, h715, h716, hc23, hlam, hphi, ht12, u1ehi3]
            · linarith only [h4, h709, h715, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h747 | h747
          · linarith only [h0, h4, h709, h747, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h749 | h749
            · rcases m.htr 1 3 4 (by decide) (by decide) with h750 | h750
              · rcases m.htr 1 4 5 (by decide) (by decide) with h751 | h751
                · linarith only [h2, h712, h751, hlam]
                · rcases h0bigk with h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p753_1, u1ehi1]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p753_1, u1ehi1]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, h712, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h0, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h4, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, h4, h712, hc23, hlam, hphi, ht12, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h1, hlam, p753_1]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h4, hc02, hc23, hlam, hphi, p753_1]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, h4, hc23, hlam, hphi, ht12, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, h4, h712, hc23, hlam, hphi, ht12, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h709, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h710, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h712, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h3, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h0, h749, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h711, hlam, p753_0]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [h2, h712, hc45, hlam, hphi, ht12, ht23, ht34, p753_1, u1ehi3]
                  · have p753_0 := h753c.1
                    have p753_1 := h753c.2.1
                    have p753_2 := h753c.2.2.1
                    have p753_3 := h753c.2.2.2
                    linarith only [hlam, p753_0]
              · linarith only [h4, h710, h747, h749, h750, hc23, hlam, hphi, ht12, u1ehi3]
            · linarith only [h4, h709, h749, hc23, hlam, hphi, ht12, u1ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
        · linarith only [h4, h709, h711, h781, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h783 | h783
          · linarith only [h0, h4, h709, h783, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
            · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
              · rcases m.htr 1 4 5 (by decide) (by decide) with h787 | h787
                · linarith only [h2, h781, h787, hlam]
                · rcases h0bigk with h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h2, h709, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, h783, h785, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, h711, h783, h785, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h0, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h4, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h4, h711, hlam, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, hlam, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h0, h785, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h2, h4, hc23, hlam, hphi, ht12, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h711, hlam, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h2, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h709, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h710, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h781, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h3, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h0, h781, h785, hc45, hlam, hphi, ht12, ht23, ht34, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h781, hc03, hc45, hlam, hphi, ht34, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h2, h781, hc45, hlam, hphi, ht12, ht23, ht34, p789_1, u1ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
              · linarith only [h4, h710, h783, h785, h786, hc23, hlam, hphi, ht12, u1ehi3]
            · linarith only [h4, h709, h785, hc12, hc23, hlam, hphi]
    · linarith only [h4, h709, h710, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h818 | h818
    · rcases m.htr 0 3 5 (by decide) (by decide) with h819 | h819
      · rcases m.htr 0 4 5 (by decide) (by decide) with h820 | h820
        · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
          · linarith only [h0, h4, h821, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h823 | h823
            · linarith only [h0, h709, h823, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h825 | h825
              · rcases m.htr 1 4 5 (by decide) (by decide) with h826 | h826
                · rcases h0bigk with h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p827_1, u1ehi1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h0, h709, h818, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p827_1, u1ehi1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h0, h709, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p827_1, u1ehi1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p827_1, u1ehi4]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h0, hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h4, hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h709, hlam, p827_1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p827_1, u1ehi4]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h1, hlam, p827_1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h4, hc02, hc23, hlam, hphi, p827_1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h2, h4, h823, hc23, hlam, hphi, ht12, p827_1, u1ehi1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h3, h4, hc23, hlam, hphi, ht12, p827_1, u1ehi4]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h2, hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p827_1, u1ehi1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h818, hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h3, h4, h818, hc23, hlam, hphi, ht12, p827_1, u1ehi4]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h3, hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p827_1, u1ehi1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h819, hlam, p827_0]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [h820, hlam, p827_1]
                  · have p827_0 := h827c.1
                    have p827_1 := h827c.2.1
                    have p827_2 := h827c.2.2.1
                    have p827_3 := h827c.2.2.2
                    linarith only [hlam, p827_0]
                · linarith only [h4, h818, h820, h823, h826, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h4, h818, h825, hc23, hlam, hphi, ht12, u1ehi2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h855 | h855
          · linarith only [h0, h4, h855, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h857 | h857
            · linarith only [h0, h709, h857, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h859 | h859
              · rcases m.htr 1 4 5 (by decide) (by decide) with h860 | h860
                · linarith only [h0, h709, h820, h859, h860, hc13, hlam, hphi, u1ehi1]
                · rcases h0bigk with h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c | h862c
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p862_1, u1ehi1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h819, hc01, hc35, hlam, hphi, ht0b, ht5b, p862_1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, h709, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p862_1, u1ehi1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h3, h860, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p862_1, u1ehi3]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h4, hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h709, hlam, p862_1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h709, h820, hlam, p862_1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h1, hlam, p862_1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p862_1, u1ehi1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, h4, h709, hc23, hlam, hphi, ht12, p862_1, u1ehi1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, h4, h709, h820, hc23, hlam, hphi, ht12, p862_1, u1ehi1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h2, hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p862_1, u1ehi1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h818, hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h820, hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h3, hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h0, h820, hc45, hlam, hphi, ht12, ht23, ht34, p862_1, u1ehi1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h819, hlam, p862_0]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [h820, hc04, hc45, hlam, hphi, p862_1]
                  · have p862_0 := h862c.1
                    have p862_1 := h862c.2.1
                    have p862_2 := h862c.2.2.1
                    have p862_3 := h862c.2.2.2
                    linarith only [hlam, p862_0]
              · linarith only [h4, h818, h859, hc23, hlam, hphi, ht12, u1ehi2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h889 | h889
        · linarith only [h818, h819, h889, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h891 | h891
          · linarith only [h0, h4, h891, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h893 | h893
            · linarith only [h0, h709, h893, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h895 | h895
              · rcases m.htr 1 4 5 (by decide) (by decide) with h896 | h896
                · linarith only [h0, h709, h889, h895, h896, hc13, hlam, hphi, u1ehi1]
                · rcases h0bigk with h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, h709, h818, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, h709, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, h709, h818, h819, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h4, hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h709, hlam, p898_1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h709, h818, h819, hlam, p898_1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h1, hlam, p898_1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, h4, h709, hc23, hlam, hphi, ht12, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h819, hlam, p898_1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h2, hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h818, hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h889, hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h3, hlam, p898_0]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h0, h889, hc45, hlam, hphi, ht12, ht23, ht34, p898_1, u1ehi1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h889, hc03, hc45, hlam, hphi, ht34, p898_1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [h889, hc04, hc45, hlam, hphi, p898_1]
                  · have p898_0 := h898c.1
                    have p898_1 := h898c.2.1
                    have p898_2 := h898c.2.2.1
                    have p898_3 := h898c.2.2.2
                    linarith only [hlam, p898_0]
              · linarith only [h4, h818, h891, h895, hc23, hlam, hphi, ht12, u1ehi1]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h925 | h925
      · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
        · rcases m.htr 1 2 3 (by decide) (by decide) with h927 | h927
          · linarith only [h0, h4, h927, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h929 | h929
            · linarith only [h0, h709, h929, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h931 | h931
              · linarith only [h1, h818, h931, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h933 | h933
                · rcases h0bigk with h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p934_1, u1ehi1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p934_1, u1ehi1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h0, h4, h818, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p934_1, u1ehi1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p934_1, u1ehi4]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h0, hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h4, hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h709, hlam, p934_1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p934_1, u1ehi4]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h1, hlam, p934_1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h818, hc02, hc34, hlam, hphi, ht23, p934_1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h818, hlam, p934_1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h3, h818, hc34, hlam, hphi, ht12, ht23, p934_1, u1ehi4]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h2, hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p934_1, u1ehi1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h818, hc03, hc34, hlam, hphi, p934_1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h3, h818, hc34, hlam, hphi, ht12, ht23, p934_1, u1ehi4]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h3, hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p934_1, u1ehi1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h925, hlam, p934_0]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [h926, hlam, p934_1]
                  · have p934_0 := h934c.1
                    have p934_1 := h934c.2.1
                    have p934_2 := h934c.2.2.1
                    have p934_3 := h934c.2.2.2
                    linarith only [hlam, p934_0]
                · linarith only [h818, h926, h927, h931, h933, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h818, h925, h926, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h962 | h962
        · rcases m.htr 1 2 3 (by decide) (by decide) with h963 | h963
          · linarith only [h0, h4, h963, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h965 | h965
            · linarith only [h0, h709, h965, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h967 | h967
              · linarith only [h1, h818, h967, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h969 | h969
                · rcases h0bigk with h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c | h970c
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, h4, h925, h962, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, h4, h925, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h4, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h709, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h4, h925, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h1, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h818, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h925, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h2, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, h709, hc24, hlam, hphi, ht12, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h818, hc03, hc34, hlam, hphi, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h3, h818, hc34, hlam, hphi, ht12, ht23, p970_1, u1ehi4]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h3, hlam, p970_0]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h1, h963, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p970_1, u1ehi1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [h962, hlam, p970_1]
                  · have p970_0 := h970c.1
                    have p970_1 := h970c.2.1
                    have p970_2 := h970c.2.2.1
                    have p970_3 := h970c.2.2.2
                    linarith only [hlam, p970_0]
                · linarith only [h818, h962, h963, h967, h969, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
          · linarith only [h0, h4, h997, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
            · linarith only [h0, h709, h999, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1001 | h1001
              · linarith only [h1, h1001, h818, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1003 | h1003
                · linarith only [h1003, h2, h962, hlam]
                · rcases h0bigk with h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c | h1005c
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1005_1, u1ehi1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1005_1, u1ehi2]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h1, h818, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1005_1, u1ehi2]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h1001, h1003, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1005_1, u1ehi2]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h0, hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h4, hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h709, hlam, p1005_1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h4, h818, h962, hlam, p1005_1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h1, hlam, p1005_1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1005_1, u1ehi1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h818, hlam, p1005_1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h925, hlam, p1005_1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h2, hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h0, h962, hc45, hlam, hphi, ht12, ht23, ht34, p1005_1, u1ehi1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h962, hc03, hc45, hlam, hphi, ht34, p1005_1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h962, hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h3, hlam, p1005_0]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h0, h962, hc45, hlam, hphi, ht12, ht23, ht34, p1005_1, u1ehi1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h1, h962, h997, hc45, hlam, hphi, ht12, ht23, ht34, p1005_1, u1ehi1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [h962, hc04, hc45, hlam, hphi, p1005_1]
                  · have p1005_0 := h1005c.1
                    have p1005_1 := h1005c.2.1
                    have p1005_2 := h1005c.2.2.1
                    have p1005_3 := h1005c.2.2.2
                    linarith only [hlam, p1005_0]

theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x0 m hb0 hb1 h0 h1 h2 h3 h4
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x0_x1 m hb0 hb1 h0 h1 h2 h3 h4

theorem r1l7_20_11_H_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]

theorem r1l7_20_11_H_I_L_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x0 m hb0 hb1 h0 h1 h2 h3
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0_x1 m hb0 hb1 h0 h1 h2 h3

theorem r1l7_20_11_H_I_L_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

theorem r1l7_20_11_H_I_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_H_I_L_R_x0_x0_x0 m hb0 hb1 h0 h1 h2
  · exact r1l7_20_11_H_I_L_R_x0_x0_x1 m hb0 hb1 h0 h1 h2

theorem r1l7_20_11_H_I_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

theorem r1l7_20_11_H_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_H_I_L_R_x0_x0 m hb0 hb1 h0 h1
  · exact r1l7_20_11_H_I_L_R_x0_x1 m hb0 hb1 h0 h1

theorem r1l7_20_11_H_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1034 | h1034
  · linarith only [h0, h1034, hc12, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1036 | h1036
    · linarith only [h0, h1036, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1038 | h1038
      · linarith only [h0, h1038, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1040 | h1040
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1041 | h1041
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1042 | h1042
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1043 | h1043
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1044 | h1044
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1045 | h1045
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1046 | h1046
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1047 | h1047
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1048 | h1048
                        · rcases h0bigk with h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h0, hlam, p1049_1]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1034, hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1036, hlam, p1049_1]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1038, hlam, p1049_1]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h0, h1038, h1042, h1044, hc12, hlam, hphi, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h0, h1038, h1044, hc12, hlam, hphi, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h0, h1038, hc12, hlam, hphi, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1040, hlam, p1049_1]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h0, h1038, h1040, h1044, hc12, hlam, hphi, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h0, h1038, h1040, hc12, hlam, hphi, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1041, hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1042, hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h0, h1038, h1040, h1042, hc12, hlam, hphi, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1049_1, u1ehi0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1040, h1042, h1044, hlam, p1049_1]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1043, hlam, p1049_0]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [h1044, hlam, p1049_1]
                          · have p1049_0 := h1049c.1
                            have p1049_1 := h1049c.2.1
                            have p1049_2 := h1049c.2.2.1
                            have p1049_3 := h1049c.2.2.2
                            linarith only [hlam, p1049_0]
                        · linarith only [h0, h1040, h1042, h1044, h1048, hc12, hlam, hphi, u1ehi3]
                      · linarith only [h0, h1040, h1042, h1047, hc12, hlam, hphi, u1ehi2]
                    · linarith only [h0, h1041, h1046, hlam]
                  · linarith only [h0, h1040, h1045, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1079 | h1079
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1080 | h1080
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1081 | h1081
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1082 | h1082
                        · linarith only [h1036, h1044, h1082, hc14, hlam, hphi, u1ehi0]
                        · linarith only [h1036, h1082, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                      · linarith only [h1034, h1081, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h1040, h1041, h1044, h1080, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1079, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1088 | h1088
                · linarith only [h1042, h1043, h1088, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1090 | h1090
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1091 | h1091
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1092 | h1092
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1093 | h1093
                        · linarith only [h1036, h1088, h1090, h1092, h1093, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1036, h1093, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                      · linarith only [h1042, h1043, h1092, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h1041, h1091, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · linarith only [h1040, h1043, h1090, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1099 | h1099
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1102 | h1102
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1103 | h1103
                      · linarith only [h1034, h1042, h1101, h1103, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h1034, h1103, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h1102, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h1040, h1101, hlam]
                · linarith only [h1042, h1099, h1100, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1109 | h1109
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1110 | h1110
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1111 | h1111
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                      · linarith only [h1034, h1042, h1110, h1112, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h1034, h1112, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h1111, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h1040, h1110, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1117 | h1117
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1119 | h1119
                      · linarith only [h1034, h1042, h1117, h1119, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h1034, h1119, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h1041, h1109, h1118, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                  · linarith only [h0, h1040, h1117, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1124 | h1124
            · linarith only [h1040, h1041, h1124, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1126 | h1126
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1127 | h1127
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1128 | h1128
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1129 | h1129
                    · linarith only [h0, h1041, h1129, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1129, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h1128, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h1040, h1041, h1126, h1127, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1134 | h1134
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1135 | h1135
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1136 | h1136
                    · linarith only [h0, h1041, h1136, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1136, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h1040, h1135, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1140 | h1140
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1141 | h1141
                    · linarith only [h0, h1041, h1141, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1141, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h1040, h1140, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1145 | h1145
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1146 | h1146
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1147 | h1147
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1148 | h1148
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1149 | h1149
                  · linarith only [h0, h1040, h1149, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1149, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1152 | h1152
                  · linarith only [h0, h1040, h1152, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1152, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1155 | h1155
                · linarith only [h1040, h1145, h1147, h1155, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1157 | h1157
                  · linarith only [h1036, h1040, h1145, h1157, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1157, hc23, hlam, hphi, ht12, u1ehi0]
            · linarith only [h1040, h1145, h1146, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1161 | h1161
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1162 | h1162
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1163 | h1163
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1164 | h1164
                  · linarith only [h0, h1040, h1164, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1164, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1167 | h1167
                  · linarith only [h0, h1040, h1167, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1167, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1170 | h1170
                · linarith only [h1161, h1162, h1170, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1172 | h1172
                  · linarith only [h0, h1040, h1172, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1172, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1175 | h1175
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1176 | h1176
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1177 | h1177
                  · linarith only [h0, h1040, h1177, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1177, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h1161, h1175, h1176, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1181 | h1181
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1182 | h1182
                  · linarith only [h0, h1040, h1182, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1182, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                  · linarith only [h0, h1040, h1185, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h1185, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_20_11_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_H_I_L_R_x0 m hb0 hb1 h0
  · exact r1l7_20_11_H_I_L_R_x1 m hb0 hb1 h0

end R2N4
