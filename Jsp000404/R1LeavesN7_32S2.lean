import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h845 | h845
  · rcases m.htr 0 2 5 (by decide) (by decide) with h846 | h846
    · rcases m.htr 0 3 4 (by decide) (by decide) with h847 | h847
      · rcases m.htr 0 3 5 (by decide) (by decide) with h848 | h848
        · rcases m.htr 0 4 5 (by decide) (by decide) with h849 | h849
          · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
            · linarith only [h4, h845, h849, h850, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h852 | h852
              · rcases h0bigk with h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h2, h845, h852, hc01, hlam, hphi, ht0b, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h2, h4, h845, h852, hc01, hlam, hphi, ht0b, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h2, h852, hc01, hlam, hphi, ht0b, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h849, hc01, hlam, hphi, ht0b, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h0, hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h4, hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h2, h4, h852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p853_1]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h1, hlam, p853_1]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p853_1]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h2, h4, h852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h4, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h2, hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h845, hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h847, hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h845, h849, hc02, hlam, hphi, ht0b, ht45, ht5b, p853_1, u4ehi4]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h3, hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h846, hlam, p853_1]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h848, hlam, p853_0]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [h849, hlam, p853_1]
                · have p853_0 := h853c.1
                  have p853_1 := h853c.2.1
                  have p853_2 := h853c.2.2.1
                  have p853_3 := h853c.2.2.2
                  linarith only [hlam, p853_0]
              · linarith only [h4, h845, h849, h852, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h880 | h880
            · linarith only [h0, h4, h846, h880, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h882 | h882
              · linarith only [h2, h849, h882, hlam]
              · rcases h0bigk with h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h846, h849, hc01, hlam, hphi, ht0b, ht45, ht5b, p884_1, u4ehi0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h847, hc01, hlam, hphi, ht0b, ht45, ht5b, p884_1, u4ehi3]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p884_1, u4ehi1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, h849, hc01, hlam, hphi, ht0b, ht45, ht5b, p884_1, u4ehi1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h0, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h4, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p884_1, u4ehi1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, h4, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p884_1, u4ehi1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h1, hlam, p884_1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p884_1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p884_1, u4ehi1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, h4, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p884_1, u4ehi1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h845, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h847, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h849, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h3, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h846, hlam, p884_1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h848, hlam, p884_0]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [h2, hc05, hlam, hphi, ht0b, ht45, ht5b, p884_1, u4ehi1]
                · have p884_0 := h884c.1
                  have p884_1 := h884c.2.1
                  have p884_2 := h884c.2.2.1
                  have p884_3 := h884c.2.2.2
                  linarith only [hlam, p884_0]
        · linarith only [h4, h846, h848, hlam]
      · linarith only [h4, h845, h847, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h912 | h912
      · rcases m.htr 0 3 5 (by decide) (by decide) with h913 | h913
        · rcases m.htr 0 4 5 (by decide) (by decide) with h914 | h914
          · linarith only [h845, h846, h914, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h916 | h916
            · linarith only [h0, h4, h916, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h918 | h918
              · linarith only [h2, h914, h918, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases h0bigk with h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h845, hc01, hlam, hphi, ht0b, ht45, ht5b, p920_1, u4ehi2]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h913, hc01, hc35, hlam, hphi, ht0b, ht5b, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p920_1, u4ehi1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h845, h846, hc01, hlam, hphi, ht0b, ht45, ht5b, p920_1, u4ehi2]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h0, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h4, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p920_1, u4ehi1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h846, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h1, hlam, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p920_1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p920_1, u4ehi1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h4, h845, h846, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p920_1, u4ehi2]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h2, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h845, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h912, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h914, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h3, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h845, hc05, hlam, hphi, ht0b, ht45, ht5b, p920_1, u4ehi2]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h913, hlam, p920_0]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [h2, h914, hc45, hlam, hphi, p920_1, u4ehi1]
                · have p920_0 := h920c.1
                  have p920_1 := h920c.2.1
                  have p920_2 := h920c.2.2.1
                  have p920_3 := h920c.2.2.2
                  linarith only [hlam, p920_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
          · linarith only [h4, h845, h913, h946, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
            · linarith only [h0, h4, h845, h948, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
              · linarith only [h2, h4, h845, h913, h946, h950, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases h0bigk with h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h845, hc01, hlam, hphi, ht0b, ht45, ht5b, p952_1, u4ehi2]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h4, h845, hc01, hlam, hphi, ht0b, ht45, ht5b, p952_1, u4ehi2]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p952_1, u4ehi0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h4, h845, h913, hc01, hlam, hphi, ht0b, ht45, ht5b, p952_1, u4ehi2]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h0, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h4, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h2, h4, h913, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p952_1, u4ehi1]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h846, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h1, hlam, p952_1]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h913, hc02, hc35, hlam, hphi, ht23, p952_1]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h2, h913, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p952_1, u4ehi1]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h913, hlam, p952_1]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h2, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h845, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h912, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h946, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h3, hlam, p952_0]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h845, hc05, hlam, hphi, ht0b, ht45, ht5b, p952_1, u4ehi2]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h913, hc03, hc35, hlam, hphi, p952_1]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [h2, h946, hc45, hlam, hphi, p952_1, u4ehi1]
                · have p952_0 := h952c.1
                  have p952_1 := h952c.2.1
                  have p952_2 := h952c.2.2.1
                  have p952_3 := h952c.2.2.2
                  linarith only [hlam, p952_0]
      · linarith only [h4, h845, h912, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h979 | h979
    · rcases m.htr 0 3 4 (by decide) (by decide) with h980 | h980
      · rcases m.htr 0 3 5 (by decide) (by decide) with h981 | h981
        · rcases m.htr 0 4 5 (by decide) (by decide) with h982 | h982
          · rcases m.htr 1 2 3 (by decide) (by decide) with h983 | h983
            · linarith only [h0, h4, h979, h983, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h985 | h985
              · rcases h0bigk with h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h3, h979, h985, hc01, hlam, hphi, ht0b, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h2, h980, h985, hc01, hlam, hphi, ht0b, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h2, h985, hc01, hlam, hphi, ht0b, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h3, h985, hc01, hlam, hphi, ht0b, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h0, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h4, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h845, hlam, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h3, h985, hc02, hlam, hphi, ht0b, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h1, hlam, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h2, h4, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h3, h4, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h2, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h3, h979, h985, hc04, hlam, hphi, ht0b, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h980, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h3, h4, h980, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p986_1, u4ehi4]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h3, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h979, hlam, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h981, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h982, hlam, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
              · rcases h0bigk with h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h979, hc01, hc25, hlam, hphi, ht0b, ht5b, p1012_1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h980, hc01, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u4ehi0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u4ehi0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h982, h985, hc01, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u4ehi1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h0, hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h4, hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h845, hlam, p1012_1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1012_1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h1, hlam, p1012_1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1012_1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h4, h982, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1012_1, u4ehi1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h4, h982, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1012_1, u4ehi1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h2, hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h979, h982, h985, hc04, hlam, hphi, ht0b, ht45, ht5b, p1012_1, u4ehi1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h980, hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h4, h980, h982, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1012_1, u4ehi1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h3, hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h979, hlam, p1012_1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h981, hlam, p1012_0]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [h982, hlam, p1012_1]
                · have p1012_0 := h1012c.1
                  have p1012_1 := h1012c.2.1
                  have p1012_2 := h1012c.2.2.1
                  have p1012_3 := h1012c.2.2.2
                  linarith only [hlam, p1012_0]
          · linarith only [h845, h979, h982, hlam]
        · linarith only [h4, h979, h981, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1040 | h1040
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1041 | h1041
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1042 | h1042
            · linarith only [h0, h1042, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1044 | h1044
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
                  linarith only [h1044, h3, h979, hc01, hlam, hphi, ht0b, ht45, ht5b, p1045_1, u4ehi4]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1040, hc01, hc35, hlam, hphi, ht0b, ht5b, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1045_1, u4ehi1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1044, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1045_1, u4ehi4]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h0, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h4, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h845, hlam, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1044, h3, hc02, hlam, hphi, ht0b, ht45, ht5b, p1045_1, u4ehi4]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1, hlam, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h980, hlam, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1044, h3, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1045_1, u4ehi4]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h2, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1044, h3, h979, hc04, hlam, hphi, ht0b, ht45, ht5b, p1045_1, u4ehi4]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h980, hc03, hc34, hlam, hphi, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1044, h3, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1045_1, u4ehi4]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h3, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h979, hlam, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1040, hlam, p1045_0]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [h1041, hlam, p1045_1]
                · have p1045_0 := h1045c.1
                  have p1045_1 := h1045c.2.1
                  have p1045_2 := h1045c.2.2.1
                  have p1045_3 := h1045c.2.2.2
                  linarith only [hlam, p1045_0]
              · rcases h0bigk with h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, h1044, h979, hc01, hlam, hphi, ht0b, ht45, ht5b, p1071_1, u4ehi1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, h1044, h4, h979, hc01, hlam, hphi, ht0b, ht45, ht5b, p1071_1, u4ehi1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1071_1, u4ehi0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, h1044, hc01, hlam, hphi, ht0b, ht45, ht5b, p1071_1, u4ehi1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h0, hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h4, hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h845, hlam, p1071_1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, h1044, hc02, hlam, hphi, ht0b, ht45, ht5b, p1071_1, u4ehi1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1, hlam, p1071_1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1071_1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h980, hlam, p1071_1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, h1044, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1071_1, u4ehi1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h2, hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, h1044, h979, hc04, hlam, hphi, ht0b, ht45, ht5b, p1071_1, u4ehi1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h980, hc03, hc34, hlam, hphi, p1071_1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, h1044, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1071_1, u4ehi1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h3, hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h979, hlam, p1071_1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1040, hlam, p1071_0]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [h1041, hlam, p1071_1]
                · have p1071_0 := h1071c.1
                  have p1071_1 := h1071c.2.1
                  have p1071_2 := h1071c.2.2.1
                  have p1071_3 := h1071c.2.2.2
                  linarith only [hlam, p1071_0]
          · linarith only [h1041, h845, h979, hlam]
        · linarith only [h1040, h4, h979, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1099 | h1099
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1100 | h1100
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1101 | h1101
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
            · linarith only [h0, h1102, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
              · rcases h0bigk with h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c | h1105c
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  rcases p1105_3 (m.d 0 1) (by simp) with h1107 | h1107
                  · rcases p1105_3 (m.d 0 2) (by simp) with h1108 | h1108
                    · linarith only [h0, h1108, hlam]
                    · rcases p1105_3 (m.d 0 3) (by simp) with h1110 | h1110
                      · linarith only [h1, h1110, hlam]
                      · linarith only [h1110, h4, hlam]
                  · linarith only [h0, h1107, hlam]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1099, h1104, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1105_1, u4ehi4]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1104, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1105_1, u4ehi4]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1104, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1105_1, u4ehi4]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h0, hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h4, hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h845, hlam, p1105_1]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h979, hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1, hlam, p1105_1]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p1105_1]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1104, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1105_1, u4ehi4]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1104, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1105_1, u4ehi4]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h2, hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h0, h845, hc12, hc24, hlam, hphi, p1105_1]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1099, hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1099, h1104, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1105_1, u4ehi4]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h3, hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1105_1]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1100, hlam, p1105_0]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [h1101, hlam, p1105_1]
                · have p1105_0 := h1105c.1
                  have p1105_1 := h1105c.2.1
                  have p1105_2 := h1105c.2.2.1
                  have p1105_3 := h1105c.2.2.2
                  linarith only [hlam, p1105_0]
              · rcases h0bigk with h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  rcases p1137_3 (m.d 0 1) (by simp) with h1139 | h1139
                  · rcases p1137_3 (m.d 0 2) (by simp) with h1140 | h1140
                    · linarith only [h0, h1140, hlam]
                    · rcases p1137_3 (m.d 0 3) (by simp) with h1142 | h1142
                      · linarith only [h1, h1142, hlam]
                      · linarith only [h1142, h4, hlam]
                  · linarith only [h0, h1139, hlam]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h1099, hc01, hlam, hphi, ht0b, ht45, ht5b, p1137_1, u4ehi0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1137_1, u4ehi0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h1101, h1104, hc01, hlam, hphi, ht0b, ht45, ht5b, p1137_1, u4ehi1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h0, hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h4, hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h845, hlam, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h979, hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h1, hlam, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h1101, h1104, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1137_1, u4ehi1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h0, h4, h979, hc12, hc23, hlam, hphi, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h2, hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h0, h845, hc12, hc24, hlam, hphi, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h1099, hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h0, h1099, h4, h979, hc12, hc23, hlam, hphi, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h3, hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h1100, hlam, p1137_0]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [h1101, hlam, p1137_1]
                · have p1137_0 := h1137c.1
                  have p1137_1 := h1137c.2.1
                  have p1137_2 := h1137c.2.2.1
                  have p1137_3 := h1137c.2.2.2
                  linarith only [hlam, p1137_0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1169 | h1169
            · linarith only [h0, h1169, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1171 | h1171
              · linarith only [h1101, h1171, h2, hlam]
              · rcases h0bigk with h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  rcases p1173_3 (m.d 0 1) (by simp) with h1175 | h1175
                  · rcases p1173_3 (m.d 0 2) (by simp) with h1176 | h1176
                    · linarith only [h0, h1176, hlam]
                    · rcases p1173_3 (m.d 0 3) (by simp) with h1178 | h1178
                      · linarith only [h1, h1178, hlam]
                      · linarith only [h1178, h4, hlam]
                  · linarith only [h0, h1175, hlam]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1100, h1101, hc01, hlam, hphi, ht0b, ht45, ht5b, p1173_1, u4ehi0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1173_1, u4ehi1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1101, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1173_1, u4ehi1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h0, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h4, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h845, hlam, p1173_1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h979, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1, hlam, p1173_1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p1173_1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1173_1, u4ehi1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1101, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1173_1, u4ehi1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h2, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h0, h1101, hc12, hc45, hlam, hphi, ht23, ht34, p1173_1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1099, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1101, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h3, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1173_1]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1100, hlam, p1173_0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [h1101, hc45, hlam, hphi, p1173_1, u4ehi0]
                · have p1173_0 := h1173c.1
                  have p1173_1 := h1173c.2.1
                  have p1173_2 := h1173c.2.2.1
                  have p1173_3 := h1173c.2.2.2
                  linarith only [hlam, p1173_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1205 | h1205
          · linarith only [h1099, h1100, h1205, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1207 | h1207
            · linarith only [h0, h1207, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1209 | h1209
              · linarith only [h1205, h1209, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases h0bigk with h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  rcases p1211_3 (m.d 0 1) (by simp) with h1213 | h1213
                  · rcases p1211_3 (m.d 0 2) (by simp) with h1214 | h1214
                    · linarith only [h0, h1214, hlam]
                    · rcases p1211_3 (m.d 0 3) (by simp) with h1216 | h1216
                      · linarith only [h1, h1216, hlam]
                      · linarith only [h1216, h4, hlam]
                  · linarith only [h0, h1213, hlam]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h1099, hc01, hlam, hphi, ht0b, ht45, ht5b, p1211_1, u4ehi3]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1211_1, u4ehi1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h1099, h1100, hc01, hlam, hphi, ht0b, ht45, ht5b, p1211_1, u4ehi3]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h0, hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h4, hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h845, hlam, p1211_1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h979, hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h1, hlam, p1211_1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1211_1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h1100, h2, h979, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1211_1, u4ehi1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h1100, hlam, p1211_1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h2, hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h0, h845, hc12, hc24, hlam, hphi, p1211_1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h1099, hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h1205, hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h3, hlam, p1211_0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1211_1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h0, h4, h979, hc12, hc25, hlam, hphi, p1211_1]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1211_1, u4ehi0]
                · have p1211_0 := h1211c.1
                  have p1211_1 := h1211c.2.1
                  have p1211_2 := h1211c.2.2.1
                  have p1211_3 := h1211c.2.2.2
                  linarith only [hlam, p1211_0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1243 | h1243
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1244 | h1244
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1245 | h1245
            · linarith only [h0, h1245, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1247 | h1247
              · rcases h0bigk with h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  rcases p1248_3 (m.d 0 1) (by simp) with h1250 | h1250
                  · rcases p1248_3 (m.d 0 2) (by simp) with h1251 | h1251
                    · linarith only [h0, h1251, hlam]
                    · rcases p1248_3 (m.d 0 3) (by simp) with h1253 | h1253
                      · linarith only [h1, h1253, hlam]
                      · linarith only [h1253, h4, hlam]
                  · linarith only [h0, h1250, hlam]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1243, h1247, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1247, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1247, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u4ehi4]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h0, hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h4, hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h845, hlam, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h979, hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1, hlam, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1099, hc02, hc34, hlam, hphi, ht23, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1099, hlam, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1099, h1247, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1248_1, u4ehi4]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h2, hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h0, h845, hc12, hc24, hlam, hphi, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1099, hc03, hc34, hlam, hphi, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1099, h1247, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1248_1, u4ehi4]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h3, hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h0, h1243, h4, hc12, hc23, hlam, hphi, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1243, hlam, p1248_0]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [h1244, hlam, p1248_1]
                · have p1248_0 := h1248c.1
                  have p1248_1 := h1248c.2.1
                  have p1248_2 := h1248c.2.2.1
                  have p1248_3 := h1248c.2.2.2
                  linarith only [hlam, p1248_0]
              · rcases h0bigk with h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  rcases p1280_3 (m.d 0 1) (by simp) with h1282 | h1282
                  · rcases p1280_3 (m.d 0 2) (by simp) with h1283 | h1283
                    · linarith only [h0, h1283, hlam]
                    · rcases p1280_3 (m.d 0 3) (by simp) with h1285 | h1285
                      · linarith only [h1, h1285, hlam]
                      · linarith only [h1285, h4, hlam]
                  · linarith only [h0, h1282, hlam]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1243, hc01, hc35, hlam, hphi, ht0b, ht5b, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1244, h1247, hc01, hlam, hphi, ht0b, ht45, ht5b, p1280_1, u4ehi1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1244, h1247, hc01, hlam, hphi, ht0b, ht45, ht5b, p1280_1, u4ehi1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h0, hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h4, hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h845, hlam, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h979, hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1, hlam, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1099, hlam, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h0, h1099, h979, hc12, hc34, hlam, hphi, ht23, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h2, hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h0, h845, hc12, hc24, hlam, hphi, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1099, hc03, hc34, hlam, hphi, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h0, h1099, h979, hc12, hc34, hlam, hphi, ht23, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h3, hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1243, hlam, p1280_0]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [h1244, hlam, p1280_1]
                · have p1280_0 := h1280c.1
                  have p1280_1 := h1280c.2.1
                  have p1280_2 := h1280c.2.2.1
                  have p1280_3 := h1280c.2.2.2
                  linarith only [hlam, p1280_0]
          · linarith only [h1099, h1243, h1244, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1313 | h1313
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1314 | h1314
            · linarith only [h0, h1314, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
              · rcases h0bigk with h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  rcases p1317_3 (m.d 0 1) (by simp) with h1319 | h1319
                  · rcases p1317_3 (m.d 0 2) (by simp) with h1320 | h1320
                    · linarith only [h0, h1320, hlam]
                    · rcases p1317_3 (m.d 0 3) (by simp) with h1322 | h1322
                      · linarith only [h1, h1322, hlam]
                      · linarith only [h1322, h4, hlam]
                  · linarith only [h0, h1319, hlam]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  rcases p1317_3 (m.d 0 1) (by simp) with h1326 | h1326
                  · rcases p1317_3 (m.d 0 2) (by simp) with h1327 | h1327
                    · linarith only [h0, h1327, hlam]
                    · rcases p1317_3 (m.d 0 3) (by simp) with h1329 | h1329
                      · linarith only [h1, h1329, hlam]
                      · rcases p1317_3 (m.d 0 4) (by simp) with h1331 | h1331
                        · linarith only [h1331, h2, hlam]
                        · linarith only [h1099, h1331, hlam]
                  · linarith only [h1, h1326, hlam]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1316, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1317_1, u4ehi4]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1316, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1317_1, u4ehi4]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h0, hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h4, hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h845, hlam, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h979, hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1, hlam, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1243, hc02, hc35, hlam, hphi, ht23, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1099, hlam, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1243, hlam, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h2, hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h0, h845, hc12, hc24, hlam, hphi, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1099, hc03, hc34, hlam, hphi, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1099, h1316, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1317_1, u4ehi4]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h3, hlam, p1317_0]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1, h1243, h1314, hc12, hc35, hlam, hphi, ht23, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [h1313, hlam, p1317_1]
                · have p1317_0 := h1317c.1
                  have p1317_1 := h1317c.2.1
                  have p1317_2 := h1317c.2.2.1
                  have p1317_3 := h1317c.2.2.2
                  linarith only [hlam, p1317_0]
              · rcases h0bigk with h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  rcases p1357_3 (m.d 0 1) (by simp) with h1359 | h1359
                  · rcases p1357_3 (m.d 0 2) (by simp) with h1360 | h1360
                    · linarith only [h0, h1360, hlam]
                    · rcases p1357_3 (m.d 0 3) (by simp) with h1362 | h1362
                      · linarith only [h1, h1362, hlam]
                      · linarith only [h1362, h4, hlam]
                  · linarith only [h0, h1359, hlam]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  rcases p1357_3 (m.d 0 1) (by simp) with h1366 | h1366
                  · rcases p1357_3 (m.d 0 2) (by simp) with h1367 | h1367
                    · linarith only [h0, h1367, hlam]
                    · rcases p1357_3 (m.d 0 3) (by simp) with h1369 | h1369
                      · linarith only [h1, h1369, hlam]
                      · rcases p1357_3 (m.d 0 4) (by simp) with h1371 | h1371
                        · linarith only [h1371, h2, hlam]
                        · linarith only [h1099, h1371, hlam]
                  · linarith only [h1, h1366, hlam]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1357_1, u4ehi0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1316, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1357_1, u4ehi1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h0, hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h4, hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h845, hlam, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h979, hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1, hlam, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1099, hlam, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1243, hlam, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h2, hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h0, h845, hc12, hc24, hlam, hphi, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1099, hc03, hc34, hlam, hphi, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1099, h1316, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1357_1, u4ehi1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h3, hlam, p1357_0]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1, h1243, h1314, hc12, hc35, hlam, hphi, ht23, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [h1313, hlam, p1357_1]
                · have p1357_0 := h1357c.1
                  have p1357_1 := h1357c.2.1
                  have p1357_2 := h1357c.2.2.1
                  have p1357_3 := h1357c.2.2.2
                  linarith only [hlam, p1357_0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1397 | h1397
            · linarith only [h0, h1397, h4, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1399 | h1399
              · linarith only [h1313, h1399, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases h0bigk with h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  rcases p1401_3 (m.d 0 1) (by simp) with h1403 | h1403
                  · rcases p1401_3 (m.d 0 2) (by simp) with h1404 | h1404
                    · linarith only [h0, h1404, hlam]
                    · rcases p1401_3 (m.d 0 3) (by simp) with h1406 | h1406
                      · linarith only [h1, h1406, hlam]
                      · linarith only [h1406, h4, hlam]
                  · linarith only [h0, h1403, hlam]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  rcases p1401_3 (m.d 0 1) (by simp) with h1410 | h1410
                  · rcases p1401_3 (m.d 0 2) (by simp) with h1411 | h1411
                    · linarith only [h0, h1411, hlam]
                    · rcases p1401_3 (m.d 0 3) (by simp) with h1413 | h1413
                      · linarith only [h1, h1413, hlam]
                      · rcases p1401_3 (m.d 0 4) (by simp) with h1415 | h1415
                        · linarith only [h1415, h2, hlam]
                        · linarith only [h1099, h1415, hlam]
                  · linarith only [h1, h1410, hlam]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1401_1, u4ehi1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1399, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1401_1, u4ehi1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h0, hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h4, hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h845, hlam, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h979, hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1, hlam, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1099, hlam, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1243, hlam, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h2, hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h0, h1313, hc12, hc45, hlam, hphi, ht23, ht34, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1313, hc03, hc45, hlam, hphi, ht34, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1313, hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h3, hlam, p1401_0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h0, h979, hc12, hc25, hlam, hphi, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1, h1243, h1397, hc12, hc35, hlam, hphi, ht23, p1401_1]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [h1313, hc45, hlam, hphi, p1401_1, u4ehi0]
                · have p1401_0 := h1401c.1
                  have p1401_1 := h1401c.2.1
                  have p1401_2 := h1401c.2.2.1
                  have p1401_3 := h1401c.2.2.2
                  linarith only [hlam, p1401_0]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0 m hb0 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x1 m hb0 hb4 h0 h1 h2 h3 h4

end R2N4
