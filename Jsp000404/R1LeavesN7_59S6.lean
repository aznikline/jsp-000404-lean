import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_59S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h5 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h749 | h749
  · linarith only [h4, h5, h749, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
    · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
      · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
        · rcases m.htr 1 3 5 (by decide) (by decide) with h754 | h754
          · linarith only [h1, h5, h754, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h756 | h756
            · linarith only [h2, h749, h756, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h758 | h758
              · rcases m.htr 2 3 5 (by decide) (by decide) with h759 | h759
                · linarith only [h2, h4, h5, h751, h759, hc12, hlam, hphi, u1ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h761 | h761
                  · linarith only [h2, h749, h751, h758, h761, hc13, hlam, hphi, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h763 | h763
                    · linarith only [h2, h749, h763, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases h3bigk with h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h5, h763, hc13, hc45, hlam, hphi, ht34, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h5, h758, h763, hc34, hc45, hlam, hphi, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h5, h763, hc34, hc45, hlam, hphi, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h5, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h1, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h758, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h1, h5, h763, hc34, hc45, hlam, hphi, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h754, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h3, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h751, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h759, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h4, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h753, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h758, hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [hlam, p765_0]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h763, hlam, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h2, h4, h763, hc45, hlam, hphi, ht12, ht23, ht34, p765_1, u1ehi3]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h763, hc13, hc45, hlam, hphi, ht34, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h758, h763, hc34, hc45, hlam, hphi, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [h763, hc34, hc45, hlam, hphi, p765_1]
                      · have p765_0 := h765c.1
                        have p765_1 := h765c.2.1
                        have p765_2 := h765c.2.2.1
                        have p765_3 := h765c.2.2.2
                        linarith only [hlam, p765_0]
              · linarith only [h4, h5, h758, hc23, hc35, hlam, hphi]
        · linarith only [h4, h5, h753, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h793 | h793
        · linarith only [h751, h752, h793, hlam]
        · linarith only [h4, h5, h793, hc35, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h3, h5, h751, hc35, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3 h4 h5
  · exact r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h797 | h797
  · rcases m.htr 0 4 5 (by decide) (by decide) with h798 | h798
    · rcases m.htr 1 2 3 (by decide) (by decide) with h799 | h799
      · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
        · rcases m.htr 1 3 4 (by decide) (by decide) with h801 | h801
          · linarith only [h0, h4, h797, h799, h801, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h803 | h803
            · rcases m.htr 1 4 5 (by decide) (by decide) with h804 | h804
              · rcases m.htr 2 3 4 (by decide) (by decide) with h805 | h805
                · linarith only [h1, h4, h799, h805, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h807 | h807
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h808 | h808
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h809 | h809
                      · rcases h3bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h803, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p810_1, u1ehi4]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h4, hc23, hc34, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h4, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h4, h809, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h1, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h807, h809, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h801, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h1, h4, h809, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h3, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h799, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h805, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h0, h3, h809, hc01, hc45, hlam, hphi, ht0b, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p810_1, u1ehi2]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          rcases p810_3 (m.d 0 3) (by simp) with h830 | h830
                          · linarith only [h4, h830, hlam]
                          · linarith only [h797, h830, hlam]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h797, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h803, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h807, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h809, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                      · linarith only [h1, h4, h803, h809, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                    · linarith only [h0, h800, h804, h805, h807, h808, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4, h797, h807, hc23, hc34, hlam, hphi]
              · linarith only [h4, h798, h804, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h4, h797, h803, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h843 | h843
          · linarith only [h1, h4, h797, h843, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h845 | h845
            · rcases m.htr 1 4 5 (by decide) (by decide) with h846 | h846
              · rcases m.htr 2 3 4 (by decide) (by decide) with h847 | h847
                · linarith only [h1, h4, h845, h847, hc23, hlam, hphi, ht12, u1ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h849 | h849
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h850 | h850
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h851 | h851
                      · rcases h3bigk with h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h799, h800, h845, h847, h849, h851, hc03, hc34, hc45, hlam, hphi, ht0b, ht12, ht23, ht5b, p852_1, u1ehi4]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h0, h3, h849, h851, hc01, hc45, hlam, hphi, ht0b, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h4, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h4, h851, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h1, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h843, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h799, h800, h847, h851, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h3, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h799, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h847, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h0, h3, h851, hc01, hc45, hlam, hphi, ht0b, ht5b, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p852_1, u1ehi2]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p852_1]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          rcases p852_3 (m.d 0 3) (by simp) with h872 | h872
                          · linarith only [h4, h872, hlam]
                          · linarith only [h797, h872, hlam]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h797, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h845, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h849, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [h851, hlam, p852_0]
                        · have p852_0 := h852c.1
                          have p852_1 := h852c.2.1
                          have p852_2 := h852c.2.2.1
                          have p852_3 := h852c.2.2.2
                          linarith only [hlam, p852_0]
                      · linarith only [h800, h847, h851, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h799, h800, h846, h850, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4, h797, h849, hc23, hc34, hlam, hphi]
              · linarith only [h4, h798, h846, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h4, h797, h845, hc13, hc34, hlam, hphi]
      · linarith only [h3, h4, h799, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h4, h797, h798, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h887 | h887
    · rcases m.htr 1 2 3 (by decide) (by decide) with h888 | h888
      · rcases m.htr 1 2 4 (by decide) (by decide) with h889 | h889
        · rcases m.htr 1 3 4 (by decide) (by decide) with h890 | h890
          · linarith only [h1, h4, h890, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h892 | h892
            · linarith only [h1, h797, h892, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h894 | h894
              · rcases m.htr 2 3 4 (by decide) (by decide) with h895 | h895
                · linarith only [h1, h4, h888, h895, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h897 | h897
                  · linarith only [h1, h797, h888, h897, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h899 | h899
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h900 | h900
                      · rcases h3bigk with h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h797, h900, hc13, hc34, hlam, hphi, p901_1]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h797, h900, hc23, hc34, hlam, hphi, p901_1]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h4, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h797, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h1, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h2, h892, h894, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h890, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h892, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h3, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h888, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h895, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h897, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p901_1]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p901_1, u1ehi2]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p901_1]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h1, h797, hc34, hlam, hphi, ht12, ht23, p901_1, u1ehi2]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p901_1, u1ehi2]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p901_1, u1ehi2]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p901_1]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [h900, hlam, p901_0]
                        · have p901_0 := h901c.1
                          have p901_1 := h901c.2.1
                          have p901_2 := h901c.2.2.1
                          have p901_3 := h901c.2.2.2
                          linarith only [hlam, p901_0]
                      · linarith only [h1, h4, h899, h900, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h928 | h928
                      · rcases h3bigk with h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p929_1, u1ehi2]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h4, hc23, hc34, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h4, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h797, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h1, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h890, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h892, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h3, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h888, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h895, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h897, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p929_1, u1ehi2]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h1, h797, hc34, hlam, hphi, ht12, ht23, p929_1, u1ehi2]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p929_1, u1ehi2]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p929_1, u1ehi2]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h928, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                      · linarith only [h0, h1, h4, h889, h894, h928, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
              · linarith only [h4, h887, h894, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h957 | h957
          · linarith only [h1, h4, h957, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h959 | h959
            · linarith only [h1, h797, h959, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h961 | h961
              · rcases m.htr 2 3 4 (by decide) (by decide) with h962 | h962
                · linarith only [h1, h4, h962, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h964 | h964
                  · linarith only [h1, h2, h797, h888, h889, h964, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h966 | h966
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h967 | h967
                      · rcases h3bigk with h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p968_1, u1ehi2]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h797, hc23, hc35, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h4, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h797, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h1, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h957, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h959, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h3, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h888, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h962, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h964, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p968_1, u1ehi2]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h1, h797, hc34, hlam, hphi, ht12, ht23, p968_1, u1ehi2]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p968_1, u1ehi2]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p968_1, u1ehi2]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p968_1]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [h967, hlam, p968_0]
                        · have p968_0 := h968c.1
                          have p968_1 := h968c.2.1
                          have p968_2 := h968c.2.2.1
                          have p968_3 := h968c.2.2.2
                          linarith only [hlam, p968_0]
                      · linarith only [h889, h962, h967, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h889, h961, h966, hlam]
              · linarith only [h4, h887, h961, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h3, h4, h888, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h998 | h998
      · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1000 | h1000
          · linarith only [h1, h1000, h4, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1002 | h1002
            · linarith only [h1, h1002, h797, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1004 | h1004
              · linarith only [h1004, h2, h887, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1006 | h1006
                · linarith only [h1, h1006, h4, h998, hc12, hlam, hphi, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1008 | h1008
                  · linarith only [h1, h1008, h797, h998, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1010 | h1010
                    · linarith only [h1, h1010, h4, h887, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1012 | h1012
                      · linarith only [h1, h1012, h4, h887, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h1, h1012, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1015 | h1015
          · linarith only [h1, h1015, h4, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1017 | h1017
            · linarith only [h1, h1017, h797, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1019 | h1019
              · linarith only [h1019, h2, h887, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1021 | h1021
                · linarith only [h1, h1021, h2, h4, h887, h998, h999, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1023 | h1023
                  · linarith only [h1, h1023, h2, h797, h887, h998, h999, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1025 | h1025
                    · linarith only [h1021, h1025, h2, h887, h998, h999, hc23, hc34, hlam, hphi]
                    · linarith only [h1025, h998, h999, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · linarith only [h3, h797, h998, hc35, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3 h4
  · exact r1l7_11_23_L_R_H_I_x0_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3 h4

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1029 | h1029
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1030 | h1030
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1031 | h1031
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1032 | h1032
        · linarith only [h0, h1032, h3, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1034 | h1034
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1035 | h1035
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1036 | h1036
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1038 | h1038
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1039 | h1039
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1040 | h1040
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1041 | h1041
                        · rcases h3bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1032, h1034, h1038, h1041, hc03, hc45, hlam, hphi, ht0b, ht5b, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h3, hlam, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1041, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            rcases p1042_3 (m.d 0 3) (by simp) with h1047 | h1047
                            · rcases p1042_3 (m.d 1 3) (by simp) with h1048 | h1048
                              · linarith only [h1, h1048, hlam]
                              · linarith only [h1036, h1048, hlam]
                            · linarith only [h1047, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1032, hlam, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1041, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht12, p1042_1, u1ehi2]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [hc23, hlam, hphi, ht12, p1042_1, u1ehi2]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1041, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            rcases p1042_3 (m.d 0 3) (by simp) with h1061 | h1061
                            · linarith only [h1061, h3, hlam]
                            · linarith only [h1030, h1061, hlam]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1029, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1035, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1038, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h0, h1034, h1038, h1041, hc02, hc45, hlam, hphi, ht0b, ht5b, p1042_1]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1030, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1036, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1039, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [h1041, hlam, p1042_0]
                          · have p1042_0 := h1042c.1
                            have p1042_1 := h1042c.2.1
                            have p1042_2 := h1042c.2.2.1
                            have p1042_3 := h1042c.2.2.2
                            linarith only [hlam, p1042_0]
                        · linarith only [h0, h1034, h1040, h1041, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1075 | h1075
                        · linarith only [h1038, h1040, h1075, hlam]
                        · rcases h3bigk with h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h3, hc23, hlam, hphi, ht12, p1077_1, u1ehi2]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h3, hlam, p1077_1]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            rcases p1077_3 (m.d 0 3) (by simp) with h1081 | h1081
                            · rcases p1077_3 (m.d 1 3) (by simp) with h1082 | h1082
                              · linarith only [h1, h1082, hlam]
                              · linarith only [h1035, h1082, hlam]
                            · linarith only [h1081, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            rcases p1077_3 (m.d 0 3) (by simp) with h1086 | h1086
                            · rcases p1077_3 (m.d 1 3) (by simp) with h1087 | h1087
                              · linarith only [h1, h1087, hlam]
                              · linarith only [h1036, h1087, hlam]
                            · linarith only [h1086, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1032, hlam, p1077_1]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1, h1075, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht12, p1077_1, u1ehi2]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [hc23, hlam, hphi, ht12, p1077_1, u1ehi2]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            rcases p1077_3 (m.d 0 3) (by simp) with h1099 | h1099
                            · linarith only [h1099, h3, hlam]
                            · linarith only [h1029, h1099, hlam]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            rcases p1077_3 (m.d 0 3) (by simp) with h1102 | h1102
                            · linarith only [h1102, h3, hlam]
                            · linarith only [h1030, h1102, hlam]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1029, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1035, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1038, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1075, hlam, p1077_1]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1030, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1036, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1039, hlam, p1077_0]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [h1030, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                          · have p1077_0 := h1077c.1
                            have p1077_1 := h1077c.2.1
                            have p1077_2 := h1077c.2.2.1
                            have p1077_3 := h1077c.2.2.2
                            linarith only [hlam, p1077_0]
                    · linarith only [h0, h1036, h1039, h3, hc13, hlam, hphi, u1ehi1]
                  · linarith only [h0, h1034, h1037, h1038, h3, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                · linarith only [h1029, h1031, h1037, h3, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h1030, h1036, h3, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h1029, h1032, h1034, h1035, h3, hc23, hlam, hphi, ht12, u1ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1120 | h1120
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1121 | h1121
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1122 | h1122
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1123 | h1123
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1124 | h1124
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1125 | h1125
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1126 | h1126
                        · rcases h3bigk with h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1034, h1120, h3, hc12, hc23, hlam, hphi, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h3, hlam, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1126, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            rcases p1127_3 (m.d 0 3) (by simp) with h1132 | h1132
                            · rcases p1127_3 (m.d 1 3) (by simp) with h1133 | h1133
                              · linarith only [h1, h1133, hlam]
                              · linarith only [h1121, h1133, hlam]
                            · linarith only [h1132, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1032, hlam, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1126, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht12, p1127_1, u1ehi2]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [hc23, hlam, hphi, ht12, p1127_1, u1ehi2]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1126, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            rcases p1127_3 (m.d 0 3) (by simp) with h1146 | h1146
                            · linarith only [h1146, h3, hlam]
                            · linarith only [h1030, h1146, hlam]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1029, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1120, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1123, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1120, h1126, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1127_1]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1030, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1121, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1124, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [h1126, hlam, p1127_0]
                          · have p1127_0 := h1127c.1
                            have p1127_1 := h1127c.2.1
                            have p1127_2 := h1127c.2.2.1
                            have p1127_3 := h1127c.2.2.2
                            linarith only [hlam, p1127_0]
                        · rcases h3bigk with h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1120, h1122, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1159_1]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h3, hlam, p1159_1]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            rcases p1159_3 (m.d 0 3) (by simp) with h1163 | h1163
                            · rcases p1159_3 (m.d 1 3) (by simp) with h1164 | h1164
                              · linarith only [h1, h1164, hlam]
                              · linarith only [h1120, h1164, hlam]
                            · linarith only [h1163, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            rcases p1159_3 (m.d 0 3) (by simp) with h1168 | h1168
                            · rcases p1159_3 (m.d 1 3) (by simp) with h1169 | h1169
                              · linarith only [h1, h1169, hlam]
                              · linarith only [h1121, h1169, hlam]
                            · linarith only [h1168, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1032, hlam, p1159_1]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1159_1]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1, h1126, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1159_1]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht12, p1159_1, u1ehi2]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [hc23, hlam, hphi, ht12, p1159_1, u1ehi2]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            rcases p1159_3 (m.d 0 3) (by simp) with h1181 | h1181
                            · linarith only [h1181, h3, hlam]
                            · linarith only [h1029, h1181, hlam]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            rcases p1159_3 (m.d 0 3) (by simp) with h1184 | h1184
                            · linarith only [h1184, h3, hlam]
                            · linarith only [h1030, h1184, hlam]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1029, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1120, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1123, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1126, hlam, p1159_1]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1030, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1121, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1124, hlam, p1159_0]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [h1030, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1159_1]
                          · have p1159_0 := h1159c.1
                            have p1159_1 := h1159c.2.1
                            have p1159_2 := h1159c.2.2.1
                            have p1159_3 := h1159c.2.2.2
                            linarith only [hlam, p1159_0]
                      · linarith only [h1034, h1122, h1125, h2, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                    · linarith only [h1, h1121, h1124, h3, hlam]
                  · linarith only [h0, h1123, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1029, h1031, h1122, h3, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h1030, h1121, h3, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h1029, h1032, h1120, h3, hc23, hlam, hphi, ht12, u1ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1203 | h1203
        · linarith only [h0, h1203, h3, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1205 | h1205
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1206 | h1206
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1207 | h1207
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1208 | h1208
                · linarith only [h1031, h1208, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1210 | h1210
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1211 | h1211
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1212 | h1212
                      · linarith only [h0, h1031, h1205, h1212, h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1214 | h1214
                        · linarith only [h0, h1031, h1205, h1210, h1214, h2, h3, hc23, hlam, hphi, ht12, u1ehi3]
                        · rcases h3bigk with h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1203, h3, hc12, hc23, hlam, hphi, p1216_1]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h3, hlam, p1216_1]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            rcases p1216_3 (m.d 0 3) (by simp) with h1220 | h1220
                            · rcases p1216_3 (m.d 1 3) (by simp) with h1221 | h1221
                              · linarith only [h1, h1221, hlam]
                              · linarith only [h1206, h1221, hlam]
                            · linarith only [h1220, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            rcases p1216_3 (m.d 0 3) (by simp) with h1225 | h1225
                            · rcases p1216_3 (m.d 1 3) (by simp) with h1226 | h1226
                              · linarith only [h1, h1226, hlam]
                              · linarith only [h1207, h1226, hlam]
                            · linarith only [h1225, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1203, hlam, p1216_1]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1216_1]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p1216_1]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, ht12, p1216_1, u1ehi2]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [hc23, hlam, hphi, ht12, p1216_1, u1ehi2]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            rcases p1216_3 (m.d 0 3) (by simp) with h1238 | h1238
                            · linarith only [h1238, h3, hlam]
                            · linarith only [h1029, h1238, hlam]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            rcases p1216_3 (m.d 0 3) (by simp) with h1241 | h1241
                            · linarith only [h1241, h3, hlam]
                            · linarith only [h1030, h1241, hlam]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1029, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1206, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1210, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1214, hlam, p1216_1]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1030, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1207, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1211, hlam, p1216_0]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [h1030, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1216_1]
                          · have p1216_0 := h1216c.1
                            have p1216_1 := h1216c.2.1
                            have p1216_2 := h1216c.2.2.1
                            have p1216_3 := h1216c.2.2.2
                            linarith only [hlam, p1216_0]
                    · linarith only [h1, h1207, h1211, h3, hlam]
                  · linarith only [h0, h1205, h1210, h3, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h1030, h1207, h3, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h1029, h1203, h1205, h1206, h3, hc23, hlam, hphi, ht12, u1ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1258 | h1258
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1259 | h1259
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1260 | h1260
                · linarith only [h1031, h1260, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1262 | h1262
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1263 | h1263
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1264 | h1264
                      · linarith only [h1031, h1205, h1264, h2, hc24, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h1205, h1264, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1, h1259, h1263, h3, hlam]
                  · linarith only [h0, h1258, h1262, h3, hc14, hlam, hphi, u1ehi1]
              · linarith only [h1030, h1205, h1258, h1259, h3, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1029, h1258, h3, hc23, hlam, hphi, ht12, u1ehi2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1271 | h1271
      · linarith only [h1029, h1030, h1271, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1273 | h1273
        · linarith only [h0, h1273, h3, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1275 | h1275
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1276 | h1276
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1277 | h1277
              · linarith only [h1, h1030, h1277, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1279 | h1279
                · linarith only [h1271, h1279, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1281 | h1281
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1282 | h1282
                    · linarith only [h0, h1030, h1275, h1282, h3, hc23, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h0, h1275, h1282, h3, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h0, h1275, h1281, h3, hc34, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h1029, h1273, h1275, h1276, h3, hc23, hlam, hphi, ht12, u1ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1287 | h1287
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1288 | h1288
              · linarith only [h1, h1030, h1288, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1290 | h1290
                · linarith only [h1271, h1290, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1292 | h1292
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1293 | h1293
                    · linarith only [h1029, h1030, h1275, h1293, h2, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h0, h1293, h3, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h1292, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h1029, h1287, h3, hc23, hlam, hphi, ht12, u1ehi2]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1298 | h1298
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1299 | h1299
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1300 | h1300
        · linarith only [h0, h1300, h3, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1302 | h1302
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1303 | h1303
            · linarith only [h1, h1029, h1298, h1303, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h1300, h1302, h1303, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1306 | h1306
            · linarith only [h0, h1029, h1306, h3, hc13, hlam, hphi, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1309 | h1309
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1310 | h1310
                  · linarith only [h0, h1029, h1310, h3, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h1310, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1029, h1299, h1300, h1306, h1309, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h1298, h1300, h1308, h3, hc23, hlam, hphi, ht12, u1ehi1]
      · linarith only [h1029, h1298, h1299, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1316 | h1316
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1317 | h1317
        · linarith only [h0, h1317, h3, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1319 | h1319
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1320 | h1320
            · linarith only [h0, h1029, h1319, h1320, h3, hc13, hlam, hphi, u1ehi3]
            · linarith only [h1317, h1319, h1320, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1323 | h1323
            · linarith only [h0, h1029, h1323, h3, hc13, hlam, hphi, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1325 | h1325
              · linarith only [h0, h1298, h1325, h3, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1327 | h1327
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1328 | h1328
                  · linarith only [h0, h1029, h1328, h3, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h1328, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1029, h1316, h1327, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1332 | h1332
        · linarith only [h0, h1332, h3, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1334 | h1334
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1335 | h1335
            · linarith only [h1, h1029, h1335, hlam]
            · linarith only [h1332, h1334, h1335, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1338 | h1338
            · linarith only [h0, h1029, h1338, h3, hc13, hlam, hphi, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1340 | h1340
              · linarith only [h1, h1298, h1340, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1342 | h1342
                · linarith only [h1316, h1342, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1344 | h1344
                  · linarith only [h0, h1029, h1344, h3, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h1344, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_23_L_R_H_I_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3
  · exact r1l7_11_23_L_R_H_I_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_23_L_R_H_I_x0_x0_x0 m hb1 hb3 h0 h1 h2
  · exact r1l7_11_23_L_R_H_I_x0_x0_x1 m hb1 hb3 h0 h1 h2

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

set_option maxHeartbeats 3508000 in
set_option maxHeartbeats 3508000 in
theorem r1l7_11_23_L_R_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_23_L_R_H_I_x0_x0 m hb1 hb3 h0 h1
  · exact r1l7_11_23_L_R_H_I_x0_x1 m hb1 hb3 h0 h1

end R2N4
