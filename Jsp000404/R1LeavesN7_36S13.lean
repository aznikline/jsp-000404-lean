import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
            · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
              · rcases h0bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h11, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h11, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h11, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, h11, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h1, hlam, p12_1]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h4, hlam, p12_1]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h11, h7, hc03, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h2, hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h5, hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h7, hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p12_1, u4ehi4]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h3, hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h6, hlam, p12_1]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h8, hlam, p12_0]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [h9, hlam, p12_1]
                · have p12_0 := h12c.1
                  have p12_1 := h12c.2.1
                  have p12_2 := h12c.2.2.1
                  have p12_3 := h12c.2.2.2
                  linarith only [hlam, p12_0]
              · linarith only [h10, h11, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
              · linarith only [h0, h10, h39, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
              · rcases h0bigk with h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h10, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h0, hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h2, h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h0, h10, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h1, hlam, p41_1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h4, hlam, p41_1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h0, h10, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h2, hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h5, hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h7, hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h10, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, p41_1, u4ehi1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h3, hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h6, hlam, p41_1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h8, hlam, p41_0]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [h9, hlam, p41_1]
                · have p41_0 := h41c.1
                  have p41_1 := h41c.2.1
                  have p41_2 := h41c.2.2.1
                  have p41_3 := h41c.2.2.2
                  linarith only [hlam, p41_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
            · linarith only [h2, h67, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
              · linarith only [h69, h7, h9, hlam]
              · rcases h0bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p71_1]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h7, hc02, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h1, hlam, p71_1]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h4, hlam, p71_1]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h7, hc03, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h2, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h5, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h7, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h9, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h3, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h6, hlam, p71_1]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h8, hlam, p71_0]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [h7, hc05, hlam, hphi, ht0b, ht45, ht5b, p71_1, u4ehi3]
                · have p71_0 := h71c.1
                  have p71_1 := h71c.2.1
                  have p71_2 := h71c.2.2.1
                  have p71_3 := h71c.2.2.2
                  linarith only [hlam, p71_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h97 | h97
          · linarith only [h7, h8, h97, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
            · linarith only [h2, h97, h99, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
              · linarith only [h101, h7, h8, h97, hlam]
              · linarith only [h101, h7, h8, hc45, hlam, hphi, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h104 | h104
        · rcases m.htr 0 4 5 (by decide) (by decide) with h105 | h105
          · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
              · rcases h0bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p108_1]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h104, h107, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h104, h107, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h104, h107, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h0, hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h104, h107, hc02, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h0, h104, h107, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h0, h104, h107, hc01, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h1, hlam, p108_1]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h4, hlam, p108_1]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h7, hlam, p108_1]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p108_1]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h2, hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h5, hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h104, h107, hc04, hlam, hphi, ht0b, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h104, h107, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p108_1, u4ehi4]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h3, hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h6, hlam, p108_1]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h104, hlam, p108_0]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [h105, hlam, p108_1]
                · have p108_0 := h108c.1
                  have p108_1 := h108c.2.1
                  have p108_2 := h108c.2.2.1
                  have p108_3 := h108c.2.2.2
                  linarith only [hlam, p108_0]
              · linarith only [h104, h106, h107, h3, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
              · linarith only [h104, h106, h135, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h104, h105, h135, h7, hc04, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h104, h105, h7, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
          · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
            · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
              · rcases h0bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  rcases p142_3 (m.d 0 1) (by simp) with h145 | h145
                  · rcases p142_3 (m.d 0 2) (by simp) with h146 | h146
                    · linarith only [h0, h146, hlam]
                    · linarith only [h146, h4, hlam]
                  · linarith only [h1, h145, hlam]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h140, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p142_1, u4ehi4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h140, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p142_1, u4ehi4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h0, hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  rcases p142_3 (m.d 0 1) (by simp) with h154 | h154
                  · rcases p142_3 (m.d 0 2) (by simp) with h155 | h155
                    · rcases p142_3 (m.d 0 3) (by simp) with h156 | h156
                      · linarith only [h156, h4, hlam]
                      · rcases p142_3 (m.d 0 4) (by simp) with h158 | h158
                        · linarith only [h158, h5, hlam]
                        · linarith only [h158, h7, hlam]
                    · linarith only [h155, h4, hlam]
                  · linarith only [h1, h154, hlam]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h0, h140, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p142_1, u4ehi4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h0, h140, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p142_1, u4ehi4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h1, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h4, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h7, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h104, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h2, hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h5, hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h7, hc03, hc34, hlam, hphi, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h140, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p142_1, u4ehi4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h3, hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h6, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h1, h104, hc13, hc35, hlam, hphi, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h139, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
              · linarith only [h140, h141, h2, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
              · rcases h0bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  rcases p182_3 (m.d 0 1) (by simp) with h185 | h185
                  · rcases p182_3 (m.d 0 2) (by simp) with h186 | h186
                    · linarith only [h0, h186, hlam]
                    · linarith only [h186, h4, hlam]
                  · linarith only [h1, h185, hlam]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h139, h140, hc01, hlam, hphi, ht0b, ht45, ht5b, p182_1, u4ehi1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h139, h140, hc01, hlam, hphi, ht0b, ht45, ht5b, p182_1, u4ehi1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h0, hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  rcases p182_3 (m.d 0 1) (by simp) with h194 | h194
                  · rcases p182_3 (m.d 0 2) (by simp) with h195 | h195
                    · rcases p182_3 (m.d 0 3) (by simp) with h196 | h196
                      · linarith only [h196, h4, hlam]
                      · rcases p182_3 (m.d 0 4) (by simp) with h198 | h198
                        · linarith only [h198, h5, hlam]
                        · linarith only [h198, h7, hlam]
                    · linarith only [h195, h4, hlam]
                  · linarith only [h1, h194, hlam]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h139, h140, hc02, hlam, hphi, ht0b, ht45, ht5b, p182_1, u4ehi1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h0, h139, h140, hc01, hlam, hphi, ht0b, ht45, ht5b, p182_1, u4ehi1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h1, hlam, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h4, hlam, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h7, hlam, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h104, hlam, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h2, hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h5, hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h1, h7, hc13, hc34, hlam, hphi, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h139, h140, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p182_1, u4ehi1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h3, hlam, p182_0]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h6, hlam, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h1, h104, h181, hc13, hc34, hlam, hphi, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [h139, hlam, p182_1]
                · have p182_0 := h182c.1
                  have p182_1 := h182c.2.1
                  have p182_2 := h182c.2.2.1
                  have p182_3 := h182c.2.2.2
                  linarith only [hlam, p182_0]
              · linarith only [h139, h181, h7, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
            · linarith only [h139, h2, h221, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h223 | h223
              · rcases h0bigk with h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  rcases p224_3 (m.d 0 1) (by simp) with h227 | h227
                  · rcases p224_3 (m.d 0 2) (by simp) with h228 | h228
                    · linarith only [h0, h228, hlam]
                    · linarith only [h228, h4, hlam]
                  · linarith only [h1, h227, hlam]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p224_1, u4ehi1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h139, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p224_1, u4ehi1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h0, hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  rcases p224_3 (m.d 0 1) (by simp) with h236 | h236
                  · rcases p224_3 (m.d 0 2) (by simp) with h237 | h237
                    · rcases p224_3 (m.d 0 3) (by simp) with h238 | h238
                      · linarith only [h238, h4, hlam]
                      · rcases p224_3 (m.d 0 4) (by simp) with h240 | h240
                        · linarith only [h240, h5, hlam]
                        · linarith only [h240, h7, hlam]
                    · linarith only [h237, h4, hlam]
                  · linarith only [h1, h236, hlam]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p224_1, u4ehi1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h0, h139, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p224_1, u4ehi1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h1, hlam, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h4, hlam, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h7, hlam, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h104, hlam, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h2, hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h5, hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h1, h139, h223, hc13, hc34, hlam, hphi, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h139, hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h3, hlam, p224_0]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h6, hlam, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h1, h104, h223, hc13, hc34, hlam, hphi, p224_1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [h139, h2, h223, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p224_1, u4ehi1]
                · have p224_0 := h224c.1
                  have p224_1 := h224c.2.1
                  have p224_2 := h224c.2.2.1
                  have p224_3 := h224c.2.2.2
                  linarith only [hlam, p224_0]
              · rcases h0bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  rcases p262_3 (m.d 0 1) (by simp) with h265 | h265
                  · rcases p262_3 (m.d 0 2) (by simp) with h266 | h266
                    · linarith only [h0, h266, hlam]
                    · linarith only [h266, h4, hlam]
                  · linarith only [h1, h265, hlam]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p262_1, u4ehi1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h139, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p262_1, u4ehi1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h0, hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  rcases p262_3 (m.d 0 1) (by simp) with h274 | h274
                  · rcases p262_3 (m.d 0 2) (by simp) with h275 | h275
                    · rcases p262_3 (m.d 0 3) (by simp) with h276 | h276
                      · linarith only [h276, h4, hlam]
                      · rcases p262_3 (m.d 0 4) (by simp) with h278 | h278
                        · linarith only [h278, h5, hlam]
                        · linarith only [h278, h7, hlam]
                    · linarith only [h275, h4, hlam]
                  · linarith only [h1, h274, hlam]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p262_1, u4ehi1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h0, h139, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p262_1, u4ehi1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h1, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h4, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h7, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h104, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h2, hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h5, hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h1, h223, h7, hc13, hc45, hlam, hphi, ht34, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h139, hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h3, hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h6, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h1, h104, h223, hc13, hc45, hlam, hphi, ht34, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h104, h223, hc45, hlam, hphi, p262_1, u4ehi0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h300 | h300
      · rcases m.htr 0 3 5 (by decide) (by decide) with h301 | h301
        · linarith only [h301, h4, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h303 | h303
          · linarith only [h300, h303, h4, h6, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
            · linarith only [h2, h303, h305, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
              · linarith only [h300, h303, h307, h4, h6, hlam]
              · linarith only [h300, h301, h307, hc45, hlam, hphi, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h310 | h310
        · linarith only [h300, h310, h5, h6, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
          · linarith only [h312, h5, h6, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h314 | h314
            · linarith only [h2, h312, h314, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h316 | h316
              · rcases h0bigk with h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  rcases p317_3 (m.d 0 1) (by simp) with h320 | h320
                  · rcases p317_3 (m.d 0 2) (by simp) with h321 | h321
                    · linarith only [h0, h321, hlam]
                    · linarith only [h321, h4, hlam]
                  · linarith only [h1, h320, hlam]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi2]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h0, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h312, h316, h6, hc03, hc34, hlam, hphi, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h2, h312, h316, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p317_1, u4ehi1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h6, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h1, hlam, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h4, hlam, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h300, hlam, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h310, hlam, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h2, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h5, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h1, h312, h316, h5, h6, hc13, hc34, hlam, hphi, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h312, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h3, hlam, p317_0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h312, h316, hc02, hc34, hlam, hphi, ht23, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h1, h312, h316, hc13, hc34, hlam, hphi, p317_1]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [h312, h316, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p317_1, u4ehi0]
                · have p317_0 := h317c.1
                  have p317_1 := h317c.2.1
                  have p317_2 := h317c.2.2.1
                  have p317_3 := h317c.2.2.2
                  linarith only [hlam, p317_0]
              · rcases h0bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi2]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  rcases p347_3 (m.d 0 1) (by simp) with h350 | h350
                  · rcases p347_3 (m.d 0 2) (by simp) with h351 | h351
                    · linarith only [h0, h351, hlam]
                    · linarith only [h351, h4, hlam]
                  · linarith only [h1, h350, hlam]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi2]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h0, hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h1, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p347_1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h2, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p347_1, u4ehi1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h6, hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h1, hlam, p347_1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h4, hlam, p347_1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h300, hlam, p347_1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h310, hlam, p347_1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h2, hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h5, hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h1, h5, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p347_1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h312, hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h3, hlam, p347_0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h5, hc05, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi0]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h1, h310, hc13, hc35, hlam, hphi, p347_1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [h2, h310, h316, hc45, hlam, hphi, p347_1, u4ehi1]
                · have p347_0 := h347c.1
                  have p347_1 := h347c.2.1
                  have p347_2 := h347c.2.2.1
                  have p347_3 := h347c.2.2.2
                  linarith only [hlam, p347_0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h377 | h377
    · rcases m.htr 0 3 4 (by decide) (by decide) with h378 | h378
      · linarith only [h378, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h380 | h380
        · rcases m.htr 0 4 5 (by decide) (by decide) with h381 | h381
          · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
            · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
              · rcases h0bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h380, h383, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi4]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h380, h383, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi4]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h380, h383, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi4]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h380, h383, hc01, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi4]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h0, hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h380, h383, hc02, hlam, hphi, ht0b, ht45, ht5b, p384_1, u4ehi4]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h5, hlam, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h5, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h1, hlam, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h4, hlam, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h378, hlam, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h3, h378, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h2, hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h378, hc02, hc34, hlam, hphi, ht23, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h378, hc03, hc34, hlam, hphi, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h378, h380, h383, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p384_1, u4ehi4]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h3, hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h377, hlam, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h380, hlam, p384_0]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [h381, hlam, p384_1]
                · have p384_0 := h384c.1
                  have p384_1 := h384c.2.1
                  have p384_2 := h384c.2.2.1
                  have p384_3 := h384c.2.2.2
                  linarith only [hlam, p384_0]
              · linarith only [h3, h377, h378, h382, h383, h5, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h411 | h411
              · linarith only [h378, h380, h382, h411, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h378, h380, h381, h411, hc04, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h380, h381, h4, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
          · rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
            · rcases m.htr 3 4 5 (by decide) (by decide) with h417 | h417
              · rcases h0bigk with h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [hlam, p418_0]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h3, h377, h416, hc01, hlam, hphi, ht0b, ht45, ht5b, p418_1, u4ehi4]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  rcases p418_3 (m.d 0 1) (by simp) with h421 | h421
                  · rcases p418_3 (m.d 0 2) (by simp) with h422 | h422
                    · linarith only [h0, h422, hlam]
                    · linarith only [h4, h422, hlam]
                  · linarith only [h1, h421, hlam]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h2, h416, hc01, hlam, hphi, ht0b, ht45, ht5b, p418_1, u4ehi4]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h3, h416, hc01, hlam, hphi, ht0b, ht45, ht5b, p418_1, u4ehi4]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h0, hlam, p418_0]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [hlam, p418_0]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h5, hlam, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h3, h416, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p418_1, u4ehi4]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h1, hlam, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h4, hlam, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [hlam, p418_0]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h378, hlam, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h380, hlam, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h2, hlam, p418_0]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h1, h378, hc13, hc34, hlam, hphi, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [hlam, p418_0]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h3, h378, h416, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p418_1, u4ehi4]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h3, hlam, p418_0]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h377, hlam, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h1, h377, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [h415, hlam, p418_1]
                · have p418_0 := h418c.1
                  have p418_1 := h418c.2.1
                  have p418_2 := h418c.2.2.1
                  have p418_3 := h418c.2.2.2
                  linarith only [hlam, p418_0]
              · linarith only [h2, h378, h416, h417, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
              · rcases h0bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [hlam, p450_0]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h378, h4, h415, h416, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1, u4ehi1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  rcases p450_3 (m.d 0 1) (by simp) with h453 | h453
                  · rcases p450_3 (m.d 0 2) (by simp) with h454 | h454
                    · linarith only [h0, h454, hlam]
                    · linarith only [h4, h454, hlam]
                  · linarith only [h1, h453, hlam]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h415, h416, hc01, hlam, hphi, ht0b, ht45, ht5b, p450_1, u4ehi1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h415, h416, hc01, hlam, hphi, ht0b, ht45, ht5b, p450_1, u4ehi1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h0, hlam, p450_0]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [hlam, p450_0]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h1, h378, h415, h416, h5, hc13, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p450_1, u4ehi1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h5, hlam, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h415, h416, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p450_1, u4ehi1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h1, hlam, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h4, hlam, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [hlam, p450_0]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h378, hlam, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h380, hlam, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h2, hlam, p450_0]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h378, hc02, hc34, hlam, hphi, ht23, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h1, h378, hc13, hc34, hlam, hphi, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [hlam, p450_0]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h378, h415, h416, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p450_1, u4ehi1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h3, hlam, p450_0]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h377, hlam, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h1, h380, hc13, hc35, hlam, hphi, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [h415, hlam, p450_1]
                · have p450_0 := h450c.1
                  have p450_1 := h450c.2.1
                  have p450_2 := h450c.2.2.1
                  have p450_3 := h450c.2.2.2
                  linarith only [hlam, p450_0]
              · linarith only [h378, h415, h449, hlam]
          · linarith only [h377, h415, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h482 | h482
      · linarith only [h4, h482, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h484 | h484
        · linarith only [h377, h4, h484, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h486 | h486
          · rcases m.htr 1 4 5 (by decide) (by decide) with h487 | h487
            · rcases m.htr 3 4 5 (by decide) (by decide) with h488 | h488
              · rcases h0bigk with h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c | h489c
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  rcases p489_3 (m.d 0 1) (by simp) with h492 | h492
                  · rcases p489_3 (m.d 0 2) (by simp) with h493 | h493
                    · linarith only [h0, h493, hlam]
                    · linarith only [h4, h493, hlam]
                  · linarith only [h1, h492, hlam]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h2, h487, hc01, hlam, hphi, ht0b, ht45, ht5b, p489_1, u4ehi4]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h377, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h0, hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h377, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h5, hlam, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h377, hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h1, hlam, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h4, hlam, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h482, hlam, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h484, hlam, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h2, hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h482, hc02, hc34, hlam, hphi, ht23, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h1, h482, hc13, hc34, hlam, hphi, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h377, h4, h482, hc23, hc34, hlam, hphi, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h3, hlam, p489_0]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h1, h484, hc13, hc35, hlam, hphi, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [h486, hlam, p489_1]
                · have p489_0 := h489c.1
                  have p489_1 := h489c.2.1
                  have p489_2 := h489c.2.2.1
                  have p489_3 := h489c.2.2.2
                  linarith only [hlam, p489_0]
              · linarith only [h482, h486, h488, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
              · rcases h0bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h4, h482, h486, h487, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p521_1, u4ehi1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  rcases p521_3 (m.d 0 1) (by simp) with h524 | h524
                  · rcases p521_3 (m.d 0 2) (by simp) with h525 | h525
                    · linarith only [h0, h525, hlam]
                    · linarith only [h4, h525, hlam]
                  · linarith only [h1, h524, hlam]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h486, h487, hc01, hlam, hphi, ht0b, ht45, ht5b, p521_1, u4ehi1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h377, h4, h482, h486, h487, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p521_1, u4ehi1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h0, hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h1, h482, h486, h487, h5, hc13, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p521_1, u4ehi1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h5, hlam, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h377, hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h1, hlam, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h4, hlam, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h482, hlam, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h484, hlam, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h2, hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h482, hc02, hc34, hlam, hphi, ht23, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h1, h482, hc13, hc34, hlam, hphi, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h377, h4, h482, hc23, hc34, hlam, hphi, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h3, hlam, p521_0]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h4, h482, h486, h487, hc05, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p521_1, u4ehi1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h1, h484, h520, hc13, hc34, hlam, hphi, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [h486, hlam, p521_1]
                · have p521_0 := h521c.1
                  have p521_1 := h521c.2.1
                  have p521_2 := h521c.2.2.1
                  have p521_3 := h521c.2.2.2
                  linarith only [hlam, p521_0]
              · linarith only [h482, h486, h520, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
            · linarith only [h2, h486, h552, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h554 | h554
              · linarith only [h4, h486, h5, h554, hc23, hc34, hlam, hphi]
              · rcases h0bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  rcases p556_3 (m.d 0 1) (by simp) with h559 | h559
                  · rcases p556_3 (m.d 0 2) (by simp) with h560 | h560
                    · linarith only [h0, h560, hlam]
                    · linarith only [h4, h560, hlam]
                  · linarith only [h1, h559, hlam]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h377, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h0, hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h1, h482, h5, hc13, hc34, hlam, hphi, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h5, hlam, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h377, hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h1, hlam, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h4, hlam, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h482, hlam, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h484, hlam, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h2, hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h482, hc02, hc34, hlam, hphi, ht23, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h1, h482, h554, hc13, hc45, hlam, hphi, ht34, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h486, hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h3, hlam, p556_0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h1, h484, hc13, hc35, hlam, hphi, p556_1]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [h486, hc45, hlam, hphi, p556_1, u4ehi0]
                · have p556_0 := h556c.1
                  have p556_1 := h556c.2.1
                  have p556_2 := h556c.2.2.1
                  have p556_3 := h556c.2.2.2
                  linarith only [hlam, p556_0]

end R2N4
