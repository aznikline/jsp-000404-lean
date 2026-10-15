import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2006 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2517 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2655 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2877 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h2878 | h2878
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2879 | h2879
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2880 | h2880
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2881 | h2881
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2882 | h2882
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2883 | h2883
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2884 | h2884
              · rcases h0bigk with h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, hlam, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2006, hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2517, hlam, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2655, hlam, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, h2880, h2884, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2885_1, u4ehi4]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, h2880, h2884, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2885_1, u4ehi4]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2877, hlam, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, h2877, h2880, h2884, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2885_1, u4ehi4]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, h2655, h2877, hc01, hc12, hlam, hphi, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2878, hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2880, hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h0, h2655, h2877, h2880, hc01, hc12, hlam, hphi, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2879, hlam, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2881, hlam, p2885_0]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [h2882, hlam, p2885_1]
                · have p2885_0 := h2885c.1
                  have p2885_1 := h2885c.2.1
                  have p2885_2 := h2885c.2.2.1
                  have p2885_3 := h2885c.2.2.2
                  linarith only [hlam, p2885_0]
              · rcases h0bigk with h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c | h2911c
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, hlam, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2006, hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2517, hlam, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2655, hlam, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, h2880, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2911_1, u4ehi0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2911_1, u4ehi0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2877, hlam, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, h2877, h2878, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2911_1, u4ehi2]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, h2655, h2877, hc01, hc12, hlam, hphi, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2878, hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2880, hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h0, h2655, h2877, h2880, hc01, hc12, hlam, hphi, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2655, h2883, hc01, hc14, hlam, hphi, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2879, hlam, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2881, hlam, p2911_0]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [h2882, hlam, p2911_1]
                · have p2911_0 := h2911c.1
                  have p2911_1 := h2911c.2.1
                  have p2911_2 := h2911c.2.2.1
                  have p2911_3 := h2911c.2.2.2
                  linarith only [hlam, p2911_0]
            · linarith only [h2517, h2882, h2883, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2938 | h2938
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2939 | h2939
              · linarith only [h2877, h2880, h2882, h2939, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases h0bigk with h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c | h2941c
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h0, hlam, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2006, hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2517, hlam, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2655, hlam, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h0, h2881, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h0, h2878, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2941_1, u4ehi2]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2877, hlam, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h0, h2877, h2878, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2941_1, u4ehi2]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h0, h2655, h2877, hc01, hc12, hlam, hphi, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2878, hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2880, hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2882, hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2655, h2938, hc01, hc14, hlam, hphi, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2879, hlam, p2941_1]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2881, hlam, p2941_0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [h2882, h2938, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2941_1, u4ehi0]
                · have p2941_0 := h2941c.1
                  have p2941_1 := h2941c.2.1
                  have p2941_2 := h2941c.2.2.1
                  have p2941_3 := h2941c.2.2.2
                  linarith only [hlam, p2941_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2967 | h2967
              · linarith only [h2517, h2938, h2967, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c | h2969c
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h0, hlam, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2006, hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2517, hlam, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2655, hlam, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h0, h2006, hc01, hc12, hlam, hphi, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2969_1, u4ehi0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2877, hlam, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h0, h2877, h2880, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2969_1, u4ehi3]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h0, h2655, h2877, hc01, hc12, hlam, hphi, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2878, hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2880, hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2882, hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2879, hlam, p2969_1]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2881, hlam, p2969_0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [h2882, hc45, hlam, hphi, p2969_1, u4ehi0]
                · have p2969_0 := h2969c.1
                  have p2969_1 := h2969c.2.1
                  have p2969_2 := h2969c.2.2.1
                  have p2969_3 := h2969c.2.2.2
                  linarith only [hlam, p2969_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2995 | h2995
          · linarith only [h2880, h2881, h2995, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2997 | h2997
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2998 | h2998
              · linarith only [h2880, h2881, h2995, h2998, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
              · linarith only [h2880, h2881, h2998, hc45, hlam, hphi, u4ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3001 | h3001
              · linarith only [h2880, h2997, h3001, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h2880, h2881, h3001, hc45, hlam, hphi, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3004 | h3004
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3005 | h3005
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3006 | h3006
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3007 | h3007
              · rcases h0bigk with h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [hlam, p3008_0]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h0, hlam, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2006, hlam, p3008_0]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2517, hlam, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2655, hlam, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [hlam, p3008_0]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h0, h3004, h3007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3008_1, u4ehi4]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h0, h2880, h3004, h3007, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3008_1, u4ehi4]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2517, h2880, hc01, hc14, hlam, hphi, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2877, hlam, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [hlam, p3008_0]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2880, hlam, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2655, h2880, hc01, hc34, hlam, hphi, ht12, ht23, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2880, hc01, hc34, hlam, hphi, ht12, ht23, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2878, hlam, p3008_0]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2880, h3004, h3007, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3008_1, u4ehi4]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [hlam, p3008_0]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2880, h3004, h3007, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3008_1, u4ehi4]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2655, h3006, hc01, hc14, hlam, hphi, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h2879, hlam, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h3004, hlam, p3008_0]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [h3005, hlam, p3008_1]
                · have p3008_0 := h3008c.1
                  have p3008_1 := h3008c.2.1
                  have p3008_2 := h3008c.2.2.1
                  have p3008_3 := h3008c.2.2.2
                  linarith only [hlam, p3008_0]
              · linarith only [h2880, h3005, h3007, hlam]
            · linarith only [h2517, h2880, h3004, h3005, h3006, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h2880, h3004, h3005, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3037 | h3037
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3038 | h3038
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3039 | h3039
              · rcases h0bigk with h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c | h3040c
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [hlam, p3040_0]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h0, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2006, hlam, p3040_0]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2517, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2655, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [hlam, p3040_0]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h0, h2006, hc01, hc12, hlam, hphi, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h0, h3037, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3040_1, u4ehi4]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h3004, hc01, hc35, hlam, hphi, ht12, ht23, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2877, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [hlam, p3040_0]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2880, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h3004, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2878, hlam, p3040_0]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2880, hc03, hc34, hlam, hphi, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [hlam, p3040_0]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2006, h2880, h3004, hc01, hc34, hlam, hphi, ht12, ht23, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2655, h3038, hc01, hc14, hlam, hphi, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2879, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h2006, h3004, hc01, hc35, hlam, hphi, ht12, ht23, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [h3037, hlam, p3040_1]
                · have p3040_0 := h3040c.1
                  have p3040_1 := h3040c.2.1
                  have p3040_2 := h3040c.2.2.1
                  have p3040_3 := h3040c.2.2.2
                  linarith only [hlam, p3040_0]
              · linarith only [h2880, h3037, h3039, hlam]
            · linarith only [h2517, h2880, h3037, h3038, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3068 | h3068
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3069 | h3069
              · rcases h0bigk with h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c | h3070c
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [hlam, p3070_0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h0, hlam, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2006, hlam, p3070_0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2517, hlam, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2655, hlam, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [hlam, p3070_0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h0, h2006, hc01, hc12, hlam, hphi, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h0, h2878, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3070_1, u4ehi2]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2877, hlam, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [hlam, p3070_0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2880, hlam, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h3004, hlam, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2878, hlam, p3070_0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2880, hc03, hc34, hlam, hphi, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [hlam, p3070_0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h3037, hlam, p3070_0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2879, hlam, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h2006, h3004, h3069, hc01, hc34, hlam, hphi, ht12, ht23, p3070_1]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [h3037, h3069, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3070_1, u4ehi0]
                · have p3070_0 := h3070c.1
                  have p3070_1 := h3070c.2.1
                  have p3070_2 := h3070c.2.2.1
                  have p3070_3 := h3070c.2.2.2
                  linarith only [hlam, p3070_0]
              · linarith only [h2006, h2880, h3068, h3069, hc01, hc14, hlam, hphi]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3097 | h3097
              · linarith only [h2517, h3068, h3097, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c | h3099c
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [hlam, p3099_0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h0, hlam, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2006, hlam, p3099_0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2517, hlam, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2655, hlam, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [hlam, p3099_0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h0, h2006, hc01, hc12, hlam, hphi, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h0, h2878, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3099_1, u4ehi2]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h0, h2655, hc01, hc12, hlam, hphi, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2880, hc01, hc34, hlam, hphi, ht12, ht23, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2877, hlam, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [hlam, p3099_0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2880, hlam, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h3004, hlam, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2878, hlam, p3099_0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2880, h3097, hc03, hc45, hlam, hphi, ht34, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [hlam, p3099_0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h3037, hlam, p3099_0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2879, hlam, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h2006, h3004, hc01, hc35, hlam, hphi, ht12, ht23, p3099_1]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [h3037, hc45, hlam, hphi, p3099_1, u4ehi0]
                · have p3099_0 := h3099c.1
                  have p3099_1 := h3099c.2.1
                  have p3099_2 := h3099c.2.2.1
                  have p3099_3 := h3099c.2.2.2
                  linarith only [hlam, p3099_0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3125 | h3125
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3126 | h3126
        · linarith only [h2877, h2879, h3126, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3128 | h3128
          · linarith only [h2877, h2879, h3125, h3128, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3130 | h3130
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3131 | h3131
              · linarith only [h2877, h2879, h3125, h3128, h3131, hlam]
              · linarith only [h3125, h3126, h3131, hc45, hlam, hphi, u4ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3134 | h3134
              · linarith only [h2517, h3125, h3130, h3134, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h3125, h3126, h3134, hc45, hlam, hphi, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3137 | h3137
        · linarith only [h2878, h2879, h3125, h3137, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3139 | h3139
          · linarith only [h2878, h2879, h3139, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3141 | h3141
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3142 | h3142
              · rcases h0bigk with h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c | h3143c
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h0, hlam, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2006, hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2517, hlam, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2655, hlam, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2006, h2655, h2879, hc01, hc15, hlam, hphi, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2655, h2879, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p3143_1, u4ehi0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2879, hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2877, hlam, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h3125, hlam, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h3137, hlam, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2878, hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2878, h2879, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h3139, hlam, p3143_0]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2879, hc01, hc25, hlam, hphi, ht12, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2879, hc02, hc25, hlam, hphi, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2006, h3137, hc01, hc35, hlam, hphi, ht12, ht23, p3143_1]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [h2878, h3139, h3142, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3143_1, u4ehi2]
                · have p3143_0 := h3143c.1
                  have p3143_1 := h3143c.2.1
                  have p3143_2 := h3143c.2.2.1
                  have p3143_3 := h3143c.2.2.2
                  linarith only [hlam, p3143_0]
              · linarith only [h2006, h3125, h3141, h3142, hc01, hc14, hlam, hphi]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3170 | h3170
              · linarith only [h2517, h3141, h3170, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c | h3172c
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h0, hlam, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2006, hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2517, hlam, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2655, hlam, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2006, h2655, h2879, h3141, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2655, h2878, h2879, h3141, hc45, hlam, hphi, p3172_1, u4ehi2]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2879, hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h3125, hc01, hc34, hlam, hphi, ht12, ht23, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2877, hlam, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h3125, hlam, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h3137, hlam, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2878, hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2878, h2879, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h3139, hlam, p3172_0]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2655, h3141, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2655, h3141, hc02, hc45, hlam, hphi, ht23, ht34, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2006, h2655, h3141, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3172_1]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [h2655, h2878, h3141, hc45, hlam, hphi, p3172_1, u4ehi2]
                · have p3172_0 := h3172c.1
                  have p3172_1 := h3172c.2.1
                  have p3172_2 := h3172c.2.2.1
                  have p3172_3 := h3172c.2.2.2
                  linarith only [hlam, p3172_0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3198 | h3198
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3199 | h3199
      · linarith only [h2877, h2878, h3199, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3201 | h3201
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3202 | h3202
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3203 | h3203
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3204 | h3204
              · rcases h0bigk with h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [hlam, p3205_0]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h0, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2006, hlam, p3205_0]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2517, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2655, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2878, hc01, hc24, hlam, hphi, ht12, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [hlam, p3205_0]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2878, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2878, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2878, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h3199, hc01, hc34, hlam, hphi, ht12, ht23, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2877, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [hlam, p3205_0]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h3199, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2655, h3199, hc01, hc34, hlam, hphi, ht12, ht23, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2878, hc02, hc24, hlam, hphi, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h3199, hc03, hc34, hlam, hphi, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [hlam, p3205_0]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h3199, h3201, h3204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3205_1, u4ehi4]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h3198, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h3201, hlam, p3205_0]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [h3202, hlam, p3205_1]
                · have p3205_0 := h3205c.1
                  have p3205_1 := h3205c.2.1
                  have p3205_2 := h3205c.2.2.1
                  have p3205_3 := h3205c.2.2.2
                  linarith only [hlam, p3205_0]
              · linarith only [h3199, h3202, h3204, hlam]
            · linarith only [h2517, h3199, h3201, h3202, h3203, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h2877, h2878, h3201, h3202, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3234 | h3234
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3235 | h3235
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3236 | h3236
              · rcases h0bigk with h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c | h3237c
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [hlam, p3237_0]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h0, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2006, hlam, p3237_0]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2517, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2655, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [hlam, p3237_0]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2006, h2517, h2878, hc01, hc14, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2878, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2517, h2655, h2878, hc01, hc14, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2006, hc01, hc13, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2877, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [hlam, p3237_0]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h3199, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h3201, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2517, h3198, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h3199, hc03, hc34, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [hlam, p3237_0]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2006, h3199, h3201, hc01, hc34, hlam, hphi, ht12, ht23, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h2655, hc01, hc15, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h3198, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h0, h2006, h3198, hc01, hc12, hlam, hphi, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [h3234, hlam, p3237_1]
                · have p3237_0 := h3237c.1
                  have p3237_1 := h3237c.2.1
                  have p3237_2 := h3237c.2.2.1
                  have p3237_3 := h3237c.2.2.2
                  linarith only [hlam, p3237_0]
              · linarith only [h3199, h3234, h3236, hlam]
            · linarith only [h2517, h3199, h3234, h3235, hc01, hc34, hlam, hphi, ht12, ht23]
          · linarith only [h2878, h3198, h3234, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3266 | h3266
      · linarith only [h2877, h2878, h3266, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3268 | h3268
        · linarith only [h2877, h3198, h3268, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3270 | h3270
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3271 | h3271
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3272 | h3272
              · rcases h0bigk with h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c | h3273c
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [hlam, p3273_0]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h0, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2006, hlam, p3273_0]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2517, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2655, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2517, h3198, h3270, hc01, hc14, hlam, hphi, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [hlam, p3273_0]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h3198, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2878, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h3198, hlam, p3273_0]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h3268, h3272, hc01, hc34, hlam, hphi, ht12, ht23, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2877, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [hlam, p3273_0]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h3266, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h3268, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2878, hc02, hc24, hlam, hphi, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h3266, hc03, hc34, hlam, hphi, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [hlam, p3273_0]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2655, h3266, hc01, hc34, hlam, hphi, ht12, ht23, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2655, h3271, hc01, hc14, hlam, hphi, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2655, h2877, h3271, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h2006, h3268, h3272, hc01, hc34, hlam, hphi, ht12, ht23, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [h3270, hlam, p3273_1]
                · have p3273_0 := h3273c.1
                  have p3273_1 := h3273c.2.1
                  have p3273_2 := h3273c.2.2.1
                  have p3273_3 := h3273c.2.2.2
                  linarith only [hlam, p3273_0]
              · linarith only [h3266, h3270, h3272, hlam]
            · linarith only [h2517, h3266, h3270, h3271, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3301 | h3301
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3302 | h3302
              · linarith only [h2877, h2878, h3270, h3302, hc23, hc34, hlam, hphi]
              · linarith only [h2006, h3266, h3301, h3302, hc01, hc14, hlam, hphi]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h3305 | h3305
              · linarith only [h2517, h3301, h3305, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases h0bigk with h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c | h3307c
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [hlam, p3307_0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h0, hlam, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2006, hlam, p3307_0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2517, hlam, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2655, hlam, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [hlam, p3307_0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2006, h2517, h2878, hc01, hc14, hlam, hphi, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2878, hlam, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3198, hlam, p3307_0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3266, hc01, hc34, hlam, hphi, ht12, ht23, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2877, hlam, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [hlam, p3307_0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3266, hlam, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3268, hlam, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2517, hc01, hc14, hlam, hphi, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h0, h2517, hc01, hc14, hlam, hphi, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3266, h3305, hc03, hc45, hlam, hphi, ht34, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [hlam, p3307_0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3270, hlam, p3307_0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3198, hc01, hc25, hlam, hphi, ht12, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2877, h3198, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h2006, h3268, hc01, hc35, hlam, hphi, ht12, ht23, p3307_1]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [h3270, hc45, hlam, hphi, p3307_1, u4ehi0]
                · have p3307_0 := h3307c.1
                  have p3307_1 := h3307c.2.1
                  have p3307_2 := h3307c.2.2.1
                  have p3307_3 := h3307c.2.2.2
                  linarith only [hlam, p3307_0]

end R2N4
