import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h757 | h757
  · rcases m.htr 0 2 5 (by decide) (by decide) with h758 | h758
    · rcases m.htr 0 3 4 (by decide) (by decide) with h759 | h759
      · rcases m.htr 0 3 5 (by decide) (by decide) with h760 | h760
        · rcases m.htr 0 4 5 (by decide) (by decide) with h761 | h761
          · rcases m.htr 1 2 3 (by decide) (by decide) with h762 | h762
            · linarith only [h4, h757, h761, h762, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
              · rcases h0bigk with h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c | h765c
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h757, h761, hc01, hlam, hphi, ht0b, ht5b, p765_1, u5ehi4]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h4, h757, h761, hc01, hlam, hphi, ht0b, ht5b, p765_1, u5ehi4]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h761, hc01, hlam, hphi, ht0b, ht5b, p765_1, u5ehi4]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p765_1, u5ehi0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h0, hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h4, hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h761, hc02, hlam, hphi, ht0b, ht5b, p765_1, u5ehi4]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p765_1, u5ehi1]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h1, hlam, p765_1]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p765_1]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h4, h761, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p765_1, u5ehi4]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p765_1, u5ehi1]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h2, hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h757, hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h759, hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h3, h757, hc02, hlam, hphi, ht0b, ht5b, p765_1, u5ehi1]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h3, hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h758, hlam, p765_1]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h760, hlam, p765_0]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [h761, hlam, p765_1]
                · have p765_0 := h765c.1
                  have p765_1 := h765c.2.1
                  have p765_2 := h765c.2.2.1
                  have p765_3 := h765c.2.2.2
                  linarith only [hlam, p765_0]
              · linarith only [h4, h758, h764, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h792 | h792
            · linarith only [h4, h758, h792, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h794 | h794
              · rcases h0bigk with h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h758, hc01, hlam, hphi, ht0b, ht5b, p795_1, u5ehi2]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h4, h758, hc01, hlam, hphi, ht0b, ht5b, p795_1, u5ehi2]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  rcases p795_3 (m.d 0 1) (by simp) with h799 | h799
                  · rcases p795_3 (m.d 0 2) (by simp) with h800 | h800
                    · linarith only [h0, h800, hlam]
                    · linarith only [h757, h800, hlam]
                  · linarith only [h2, h799, hlam]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p795_1, u5ehi0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h0, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h4, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p795_1]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p795_1, u5ehi1]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h1, hlam, p795_1]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p795_1]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  rcases p795_3 (m.d 0 1) (by simp) with h813 | h813
                  · rcases p795_3 (m.d 0 2) (by simp) with h814 | h814
                    · linarith only [h4, h814, hlam]
                    · linarith only [h757, h814, hlam]
                  · linarith only [h2, h813, hlam]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p795_1, u5ehi1]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h2, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h757, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h759, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h761, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h3, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h758, hlam, p795_1]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h760, hlam, p795_0]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [h4, h757, h758, h794, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p795_1]
                · have p795_0 := h795c.1
                  have p795_1 := h795c.2.1
                  have p795_2 := h795c.2.2.1
                  have p795_3 := h795c.2.2.2
                  linarith only [hlam, p795_0]
              · linarith only [h4, h758, h794, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h4, h758, h760, hlam]
      · linarith only [h4, h757, h759, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h832 | h832
      · rcases m.htr 0 3 5 (by decide) (by decide) with h833 | h833
        · rcases m.htr 0 4 5 (by decide) (by decide) with h834 | h834
          · linarith only [h757, h758, h834, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h836 | h836
            · linarith only [h0, h4, h757, h836, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h838 | h838
              · rcases h0bigk with h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c | h839c
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h757, h838, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h833, hc01, hlam, hphi, ht0b, ht5b, p839_1, u5ehi0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  rcases p839_3 (m.d 0 1) (by simp) with h843 | h843
                  · rcases p839_3 (m.d 0 2) (by simp) with h844 | h844
                    · linarith only [h0, h844, hlam]
                    · linarith only [h757, h844, hlam]
                  · linarith only [h2, h843, hlam]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h757, h758, h838, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h0, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h4, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h758, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h1, hlam, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  rcases p839_3 (m.d 0 1) (by simp) with h857 | h857
                  · rcases p839_3 (m.d 0 2) (by simp) with h858 | h858
                    · linarith only [h4, h858, hlam]
                    · linarith only [h757, h858, hlam]
                  · linarith only [h2, h857, hlam]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h4, h757, h758, h838, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h2, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h757, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h832, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h834, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h3, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h757, h838, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h833, hlam, p839_0]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [h757, h834, h838, hc34, hc45, hlam, hphi, p839_1]
                · have p839_0 := h839c.1
                  have p839_1 := h839c.2.1
                  have p839_2 := h839c.2.2.1
                  have p839_3 := h839c.2.2.2
                  linarith only [hlam, p839_0]
              · linarith only [h4, h757, h832, h838, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h874 | h874
          · linarith only [h757, h758, h874, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h876 | h876
            · linarith only [h0, h4, h757, h876, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h878 | h878
              · rcases h0bigk with h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h757, h878, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h4, h757, h878, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  rcases p879_3 (m.d 0 1) (by simp) with h883 | h883
                  · rcases p879_3 (m.d 0 2) (by simp) with h884 | h884
                    · linarith only [h0, h884, hlam]
                    · linarith only [h757, h884, hlam]
                  · linarith only [h2, h883, hlam]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h4, h757, h833, h878, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h0, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h4, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h758, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h1, hlam, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h757, h833, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h757, h833, h878, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h833, hlam, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h2, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h757, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h832, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h874, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h3, hlam, p879_0]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h757, h758, h878, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h833, hc03, hc35, hlam, hphi, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [h757, h874, h878, hc34, hc45, hlam, hphi, p879_1]
                · have p879_0 := h879c.1
                  have p879_1 := h879c.2.1
                  have p879_2 := h879c.2.2.1
                  have p879_3 := h879c.2.2.2
                  linarith only [hlam, p879_0]
              · linarith only [h4, h757, h832, h878, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h4, h757, h832, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h911 | h911
    · rcases m.htr 0 3 4 (by decide) (by decide) with h912 | h912
      · rcases m.htr 0 3 5 (by decide) (by decide) with h913 | h913
        · rcases m.htr 0 4 5 (by decide) (by decide) with h914 | h914
          · rcases m.htr 1 2 3 (by decide) (by decide) with h915 | h915
            · linarith only [h4, h911, h915, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h917 | h917
              · rcases h0bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h911, hc01, hlam, hphi, ht0b, ht5b, p918_1, u5ehi2]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h757, h911, h912, hc01, hlam, hphi, ht0b, ht5b, p918_1, u5ehi2]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h757, h911, hc01, hlam, hphi, ht0b, ht5b, p918_1, u5ehi2]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p918_1, u5ehi0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h0, hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h4, hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h757, hlam, p918_1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h3, hc02, hlam, hphi, ht0b, ht5b, p918_1, u5ehi1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h1, hlam, p918_1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p918_1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h4, h914, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p918_1, u5ehi4]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p918_1, u5ehi1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h2, hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h911, hc04, hlam, hphi, ht0b, ht5b, p918_1, u5ehi2]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h912, hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h3, h757, h917, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p918_1, u5ehi1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h3, hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h911, hlam, p918_1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h913, hlam, p918_0]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [h914, hlam, p918_1]
                · have p918_0 := h918c.1
                  have p918_1 := h918c.2.1
                  have p918_2 := h918c.2.2.1
                  have p918_3 := h918c.2.2.2
                  linarith only [hlam, p918_0]
              · linarith only [h4, h912, h917, hlam]
          · linarith only [h757, h911, h914, hlam]
        · linarith only [h4, h911, h913, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h947 | h947
        · rcases m.htr 0 4 5 (by decide) (by decide) with h948 | h948
          · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
            · linarith only [h0, h4, h949, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h951 | h951
              · linarith only [h4, h911, h912, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h4, h911, h951, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · linarith only [h757, h911, h948, hlam]
        · linarith only [h4, h911, h947, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h956 | h956
      · rcases m.htr 0 3 5 (by decide) (by decide) with h957 | h957
        · rcases m.htr 0 4 5 (by decide) (by decide) with h958 | h958
          · rcases m.htr 1 2 3 (by decide) (by decide) with h959 | h959
            · linarith only [h0, h4, h959, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h961 | h961
              · rcases h0bigk with h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  rcases p962_3 (m.d 0 1) (by simp) with h964 | h964
                  · rcases p962_3 (m.d 0 2) (by simp) with h965 | h965
                    · linarith only [h0, h965, hlam]
                    · rcases p962_3 (m.d 0 3) (by simp) with h967 | h967
                      · linarith only [h1, h967, hlam]
                      · linarith only [h4, h967, hlam]
                  · linarith only [h0, h964, hlam]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h956, h958, hc01, hlam, hphi, ht0b, ht5b, p962_1, u5ehi4]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h958, hc01, hlam, hphi, ht0b, ht5b, p962_1, u5ehi4]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p962_1, u5ehi1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h0, hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h4, hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h757, hlam, p962_1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h911, hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h1, hlam, p962_1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p962_1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h0, h4, h757, hc12, hc23, hlam, hphi, p962_1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p962_1, u5ehi1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h2, hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h0, h757, hc12, hc24, hlam, hphi, p962_1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h956, hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h3, h4, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p962_1, u5ehi1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h3, hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p962_1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h957, hlam, p962_0]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [h958, hlam, p962_1]
                · have p962_0 := h962c.1
                  have p962_1 := h962c.2.1
                  have p962_2 := h962c.2.2.1
                  have p962_3 := h962c.2.2.2
                  linarith only [hlam, p962_0]
              · linarith only [h4, h956, h961, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h995 | h995
            · linarith only [h0, h4, h995, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h997 | h997
              · rcases h0bigk with h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c | h998c
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  rcases p998_3 (m.d 0 1) (by simp) with h1000 | h1000
                  · rcases p998_3 (m.d 0 2) (by simp) with h1001 | h1001
                    · linarith only [h0, h1001, hlam]
                    · rcases p998_3 (m.d 0 3) (by simp) with h1003 | h1003
                      · linarith only [h1, h1003, hlam]
                      · linarith only [h1003, h4, hlam]
                  · linarith only [h0, h1000, hlam]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h957, hc01, hlam, hphi, ht0b, ht5b, p998_1, u5ehi3]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  rcases p998_3 (m.d 0 1) (by simp) with h1008 | h1008
                  · rcases p998_3 (m.d 0 2) (by simp) with h1009 | h1009
                    · linarith only [h0, h1009, hlam]
                    · rcases p998_3 (m.d 0 3) (by simp) with h1011 | h1011
                      · linarith only [h1, h1011, hlam]
                      · linarith only [h1011, h956, hlam]
                  · linarith only [h1008, h2, hlam]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p998_1, u5ehi0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h0, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h4, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h757, hlam, p998_1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h911, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h1, hlam, p998_1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p998_1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h0, h4, h757, hc12, hc23, hlam, hphi, p998_1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p998_1, u5ehi1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h2, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h0, h757, h997, hc12, hc23, hlam, hphi, p998_1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h956, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h958, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h3, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p998_1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h957, hlam, p998_0]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [h958, hc04, hc45, hlam, hphi, p998_1]
                · have p998_0 := h998c.1
                  have p998_1 := h998c.2.1
                  have p998_2 := h998c.2.2.1
                  have p998_3 := h998c.2.2.2
                  linarith only [hlam, p998_0]
              · linarith only [h4, h956, h997, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1037 | h1037
          · linarith only [h1037, h956, h957, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1039 | h1039
            · linarith only [h0, h1039, h4, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1041 | h1041
              · rcases h0bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  rcases p1042_3 (m.d 0 1) (by simp) with h1044 | h1044
                  · rcases p1042_3 (m.d 0 2) (by simp) with h1045 | h1045
                    · linarith only [h0, h1045, hlam]
                    · rcases p1042_3 (m.d 0 3) (by simp) with h1047 | h1047
                      · linarith only [h1, h1047, hlam]
                      · linarith only [h1047, h4, hlam]
                  · linarith only [h0, h1044, hlam]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h956, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  rcases p1042_3 (m.d 0 1) (by simp) with h1052 | h1052
                  · rcases p1042_3 (m.d 0 2) (by simp) with h1053 | h1053
                    · linarith only [h0, h1053, hlam]
                    · rcases p1042_3 (m.d 0 3) (by simp) with h1055 | h1055
                      · linarith only [h1, h1055, hlam]
                      · linarith only [h1055, h956, hlam]
                  · linarith only [h1052, h2, hlam]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h956, h957, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h0, hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h4, hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h757, hlam, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h911, hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h1, hlam, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h0, h957, hc12, hc35, hlam, hphi, ht23, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h0, h757, h957, hc12, hc35, hlam, hphi, ht23, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h957, hlam, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h2, hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h0, h1037, hc12, hc45, hlam, hphi, ht23, ht34, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h956, hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h1037, hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h3, hlam, p1042_0]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h957, hc03, hc35, hlam, hphi, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [h1037, hc04, hc45, hlam, hphi, p1042_1]
                · have p1042_0 := h1042c.1
                  have p1042_1 := h1042c.2.1
                  have p1042_2 := h1042c.2.2.1
                  have p1042_3 := h1042c.2.2.2
                  linarith only [hlam, p1042_0]
              · linarith only [h1041, h4, h956, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1081 | h1081
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1082 | h1082
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1083 | h1083
            · linarith only [h0, h1083, h4, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1085 | h1085
              · linarith only [h1081, h1085, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases h0bigk with h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  rcases p1087_3 (m.d 0 1) (by simp) with h1089 | h1089
                  · rcases p1087_3 (m.d 0 2) (by simp) with h1090 | h1090
                    · linarith only [h0, h1090, hlam]
                    · rcases p1087_3 (m.d 0 3) (by simp) with h1092 | h1092
                      · linarith only [h1, h1092, hlam]
                      · linarith only [h1092, h4, hlam]
                  · linarith only [h0, h1089, hlam]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1081, hc01, hlam, hphi, ht0b, ht5b, p1087_1, u5ehi3]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1081, h956, hc01, hlam, hphi, ht0b, ht5b, p1087_1, u5ehi3]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p1087_1, u5ehi0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h4, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h757, hlam, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h911, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1, hlam, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, h1085, h4, hc12, hc34, hlam, hphi, ht23, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h956, hlam, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1085, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1087_1, u5ehi1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h2, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, h1085, h757, hc12, hc34, hlam, hphi, ht23, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1085, h757, hc03, hc34, hlam, hphi, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1085, h3, h757, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1087_1, u5ehi1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h3, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1081, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1082, hlam, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
          · linarith only [h1081, h1082, h956, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1120 | h1120
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1121 | h1121
            · linarith only [h0, h1121, h4, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1123 | h1123
              · rcases h0bigk with h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  rcases p1124_3 (m.d 0 1) (by simp) with h1126 | h1126
                  · rcases p1124_3 (m.d 0 2) (by simp) with h1127 | h1127
                    · linarith only [h0, h1127, hlam]
                    · rcases p1124_3 (m.d 0 3) (by simp) with h1129 | h1129
                      · linarith only [h1, h1129, hlam]
                      · linarith only [h1129, h4, hlam]
                  · linarith only [h0, h1126, hlam]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  rcases p1124_3 (m.d 0 1) (by simp) with h1133 | h1133
                  · rcases p1124_3 (m.d 0 2) (by simp) with h1134 | h1134
                    · linarith only [h0, h1134, hlam]
                    · rcases p1124_3 (m.d 0 3) (by simp) with h1136 | h1136
                      · linarith only [h1, h1136, hlam]
                      · rcases p1124_3 (m.d 0 4) (by simp) with h1138 | h1138
                        · linarith only [h1138, h2, hlam]
                        · linarith only [h1138, h956, hlam]
                  · linarith only [h1, h1133, hlam]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h1120, hc01, hlam, hphi, ht0b, ht5b, p1124_1, u5ehi4]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1124_1, u5ehi1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h0, hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h4, hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h757, hlam, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h911, hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h1, hlam, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h0, h1081, hc12, hc35, hlam, hphi, ht23, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h956, hlam, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h1081, hlam, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h2, hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h0, h757, hc12, hc24, hlam, hphi, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h1123, h956, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h1123, h3, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1124_1, u5ehi1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h3, hlam, p1124_0]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h0, h1081, h4, hc12, hc35, hlam, hphi, ht23, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [h1120, hlam, p1124_1]
                · have p1124_0 := h1124c.1
                  have p1124_1 := h1124c.2.1
                  have p1124_2 := h1124c.2.2.1
                  have p1124_3 := h1124c.2.2.2
                  linarith only [hlam, p1124_0]
              · rcases h0bigk with h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c | h1164c
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  rcases p1164_3 (m.d 0 1) (by simp) with h1166 | h1166
                  · rcases p1164_3 (m.d 0 2) (by simp) with h1167 | h1167
                    · linarith only [h0, h1167, hlam]
                    · rcases p1164_3 (m.d 0 3) (by simp) with h1169 | h1169
                      · linarith only [h1, h1169, hlam]
                      · linarith only [h1169, h4, hlam]
                  · linarith only [h0, h1166, hlam]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  rcases p1164_3 (m.d 0 1) (by simp) with h1173 | h1173
                  · rcases p1164_3 (m.d 0 2) (by simp) with h1174 | h1174
                    · linarith only [h0, h1174, hlam]
                    · rcases p1164_3 (m.d 0 3) (by simp) with h1176 | h1176
                      · linarith only [h1, h1176, hlam]
                      · rcases p1164_3 (m.d 0 4) (by simp) with h1178 | h1178
                        · linarith only [h1178, h2, hlam]
                        · linarith only [h1178, h956, hlam]
                  · linarith only [h1, h1173, hlam]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1120, hc01, hlam, hphi, ht0b, ht5b, p1164_1, u5ehi0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p1164_1, u5ehi0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h4, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h757, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h911, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, h1123, h4, hc12, hc34, hlam, hphi, ht23, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h956, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1081, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h2, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, h1123, h757, hc12, hc34, hlam, hphi, ht23, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1123, h757, hc03, hc34, hlam, hphi, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1123, h3, h757, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1164_1, u5ehi1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h3, hlam, p1164_0]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1, h1081, h1121, hc12, hc35, hlam, hphi, ht23, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [h1120, hlam, p1164_1]
                · have p1164_0 := h1164c.1
                  have p1164_1 := h1164c.2.1
                  have p1164_2 := h1164c.2.2.1
                  have p1164_3 := h1164c.2.2.2
                  linarith only [hlam, p1164_0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1204 | h1204
            · linarith only [h0, h1204, h4, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1206 | h1206
              · rcases h0bigk with h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  rcases p1207_3 (m.d 0 1) (by simp) with h1209 | h1209
                  · rcases p1207_3 (m.d 0 2) (by simp) with h1210 | h1210
                    · linarith only [h0, h1210, hlam]
                    · rcases p1207_3 (m.d 0 3) (by simp) with h1212 | h1212
                      · linarith only [h1, h1212, hlam]
                      · linarith only [h1212, h4, hlam]
                  · linarith only [h0, h1209, hlam]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  rcases p1207_3 (m.d 0 1) (by simp) with h1216 | h1216
                  · rcases p1207_3 (m.d 0 2) (by simp) with h1217 | h1217
                    · linarith only [h0, h1217, hlam]
                    · rcases p1207_3 (m.d 0 3) (by simp) with h1219 | h1219
                      · linarith only [h1, h1219, hlam]
                      · rcases p1207_3 (m.d 0 4) (by simp) with h1221 | h1221
                        · linarith only [h1221, h2, hlam]
                        · linarith only [h1221, h956, hlam]
                  · linarith only [h1, h1216, hlam]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  rcases p1207_3 (m.d 0 1) (by simp) with h1225 | h1225
                  · rcases p1207_3 (m.d 0 2) (by simp) with h1226 | h1226
                    · linarith only [h0, h1226, hlam]
                    · rcases p1207_3 (m.d 0 3) (by simp) with h1228 | h1228
                      · linarith only [h1, h1228, hlam]
                      · rcases p1207_3 (m.d 0 4) (by simp) with h1230 | h1230
                        · linarith only [h1230, h2, hlam]
                        · rcases p1207_3 (m.d 0 5) (by simp) with h1232 | h1232
                          · linarith only [h1232, h3, hlam]
                          · linarith only [h1120, h1232, hlam]
                  · linarith only [h1225, h2, hlam]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p1207_1, u5ehi0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h0, hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h4, hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h757, hlam, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h911, hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h1, hlam, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h956, hlam, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h1081, hlam, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h2, hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h0, h757, hc12, hc24, hlam, hphi, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h0, h4, h757, hc12, hc24, hlam, hphi, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h1120, hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h3, hlam, p1207_0]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h0, h1081, h4, hc12, hc35, hlam, hphi, ht23, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [h1120, hc04, hc45, hlam, hphi, p1207_1]
                · have p1207_0 := h1207c.1
                  have p1207_1 := h1207c.2.1
                  have p1207_2 := h1207c.2.2.1
                  have p1207_3 := h1207c.2.2.2
                  linarith only [hlam, p1207_0]
              · rcases h0bigk with h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  rcases p1257_3 (m.d 0 1) (by simp) with h1259 | h1259
                  · rcases p1257_3 (m.d 0 2) (by simp) with h1260 | h1260
                    · linarith only [h0, h1260, hlam]
                    · rcases p1257_3 (m.d 0 3) (by simp) with h1262 | h1262
                      · linarith only [h1, h1262, hlam]
                      · linarith only [h1262, h4, hlam]
                  · linarith only [h0, h1259, hlam]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  rcases p1257_3 (m.d 0 1) (by simp) with h1266 | h1266
                  · rcases p1257_3 (m.d 0 2) (by simp) with h1267 | h1267
                    · linarith only [h0, h1267, hlam]
                    · rcases p1257_3 (m.d 0 3) (by simp) with h1269 | h1269
                      · linarith only [h1, h1269, hlam]
                      · rcases p1257_3 (m.d 0 4) (by simp) with h1271 | h1271
                        · linarith only [h1271, h2, hlam]
                        · linarith only [h1271, h956, hlam]
                  · linarith only [h1, h1266, hlam]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  rcases p1257_3 (m.d 0 1) (by simp) with h1275 | h1275
                  · rcases p1257_3 (m.d 0 2) (by simp) with h1276 | h1276
                    · linarith only [h0, h1276, hlam]
                    · rcases p1257_3 (m.d 0 3) (by simp) with h1278 | h1278
                      · linarith only [h1, h1278, hlam]
                      · rcases p1257_3 (m.d 0 4) (by simp) with h1280 | h1280
                        · linarith only [h1280, h2, hlam]
                        · rcases p1257_3 (m.d 0 5) (by simp) with h1282 | h1282
                          · linarith only [h1282, h3, hlam]
                          · linarith only [h1120, h1282, hlam]
                  · linarith only [h1275, h2, hlam]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht5b, p1257_1, u5ehi0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h0, hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h4, hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h757, hlam, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h911, hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h1, hlam, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h0, h1206, h4, hc12, hc34, hlam, hphi, ht23, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h956, hlam, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h1081, hlam, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h2, hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h0, h1206, h757, hc12, hc34, hlam, hphi, ht23, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h1206, h757, hc03, hc34, hlam, hphi, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h1120, hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h3, hlam, p1257_0]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h0, h911, hc12, hc25, hlam, hphi, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h0, h1081, h4, hc12, hc35, hlam, hphi, ht23, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [h1120, hc04, hc45, hlam, hphi, p1257_1]
                · have p1257_0 := h1257c.1
                  have p1257_1 := h1257c.2.1
                  have p1257_2 := h1257c.2.2.1
                  have p1257_3 := h1257c.2.2.2
                  linarith only [hlam, p1257_0]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

end R2N4
