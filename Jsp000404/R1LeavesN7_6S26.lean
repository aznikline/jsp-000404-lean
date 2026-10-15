import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15246 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15483 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h15484 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  rcases m.htr 0 4 5 (by decide) (by decide) with h15485 | h15485
  · rcases m.htr 1 2 3 (by decide) (by decide) with h15486 | h15486
    · rcases m.htr 1 2 4 (by decide) (by decide) with h15487 | h15487
      · rcases m.htr 1 2 5 (by decide) (by decide) with h15488 | h15488
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15489 | h15489
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15490 | h15490
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15491 | h15491
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15492 | h15492
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15493 | h15493
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15494 | h15494
                    · rcases h0bigk with h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c | h15495c
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h0, hlam, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h6793, hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h10058, hlam, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h11024, hlam, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h15246, h15486, h15491, h15493, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h11558, hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h14803, hlam, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h15246, hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h11558, h15486, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h0, h11558, h15486, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h10058, h11558, h15486, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h0, h11558, h15246, h15486, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h14803, h15486, h15491, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h0, h14803, h15486, h15491, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h15483, hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h0, h14803, h15246, h15486, h15491, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h15246, h15486, h15491, h15493, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h0, h15246, h15486, h15491, h15493, hc01, hc12, hlam, hphi, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h15484, hlam, p15495_0]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [h15485, hlam, p15495_1]
                      · have p15495_0 := h15495c.1
                        have p15495_1 := h15495c.2.1
                        have p15495_2 := h15495c.2.2.1
                        have p15495_3 := h15495c.2.2.2
                        linarith only [hlam, p15495_0]
                    · rcases h0bigk with h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c | h15521c
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h0, hlam, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h6793, hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h10058, hlam, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h11024, hlam, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h11558, h15486, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h11558, hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h14803, hlam, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h15246, hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h11558, h15486, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h0, h11558, h15486, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h11558, h15485, h15486, h15494, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h11024, h11558, h15486, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h14803, h15486, h15491, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h0, h14803, h15486, h15491, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h15483, hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h0, h14803, h15246, h15486, h15491, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h15246, h15486, h15491, h15493, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h0, h15246, h15486, h15491, h15493, hc01, hc12, hlam, hphi, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h15484, hlam, p15521_0]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [h15485, hlam, p15521_1]
                      · have p15521_0 := h15521c.1
                        have p15521_1 := h15521c.2.1
                        have p15521_2 := h15521c.2.2.1
                        have p15521_3 := h15521c.2.2.2
                        linarith only [hlam, p15521_0]
                  · linarith only [h14803, h15485, h15493, hlam]
                · linarith only [h11558, h15484, h15492, hlam]
              · linarith only [h11558, h15483, h15491, hlam]
            · linarith only [h14803, h15485, h15487, h15490, hlam]
          · linarith only [h11558, h15483, h15486, h15489, hlam]
        · linarith only [h0, h11558, h15486, h15488, hc01, hc25, hlam, hphi, ht12]
      · linarith only [h0, h11558, h15486, h15487, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h15554 | h15554
      · linarith only [h0, h14803, h15486, h15554, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h15556 | h15556
        · linarith only [h0, h15246, h15486, h15556, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15558 | h15558
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15559 | h15559
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15560 | h15560
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15561 | h15561
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15562 | h15562
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15563 | h15563
                    · rcases h0bigk with h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c | h15564c
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h0, hlam, p15564_1]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h6793, hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h10058, hlam, p15564_1]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h11024, hlam, p15564_1]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h0, h15556, h15560, h15562, hc01, hc23, hlam, hphi, ht12, p15564_1]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h11558, hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h14803, hlam, p15564_1]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h15246, hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15575 | h15575
                        · linarith only [h15575, h6793, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15577 | h15577
                          · linarith only [h11558, h15577, hlam]
                          · linarith only [h0, h15577, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15580 | h15580
                        · linarith only [h15580, h6793, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15582 | h15582
                          · linarith only [h11558, h15582, hlam]
                          · rcases p15564_3 (m.d 0 3) (by simp) with h15584 | h15584
                            · rcases p15564_3 (m.d 0 4) (by simp) with h15585 | h15585
                              · linarith only [h15483, h15585, hlam]
                              · linarith only [h14803, h15585, hlam]
                            · linarith only [h11558, h15584, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h15483, h15563, hc45, hlam, hphi, ht0b, ht5b, p15564_1, u0elo2]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15591 | h15591
                        · linarith only [h15591, h6793, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15593 | h15593
                          · linarith only [h11558, h15593, hlam]
                          · rcases p15564_3 (m.d 0 3) (by simp) with h15595 | h15595
                            · rcases p15564_3 (m.d 0 4) (by simp) with h15596 | h15596
                              · linarith only [h15483, h15596, hlam]
                              · linarith only [h15485, h15596, hlam]
                            · linarith only [h15484, h15595, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15600 | h15600
                        · linarith only [h10058, h15600, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15602 | h15602
                          · linarith only [h14803, h15602, hlam]
                          · linarith only [h0, h15602, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15605 | h15605
                        · linarith only [h10058, h15605, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15607 | h15607
                          · linarith only [h14803, h15607, hlam]
                          · rcases p15564_3 (m.d 0 3) (by simp) with h15609 | h15609
                            · rcases p15564_3 (m.d 0 4) (by simp) with h15610 | h15610
                              · rcases p15564_3 (m.d 0 5) (by simp) with h15611 | h15611
                                · linarith only [h15485, h15611, hlam]
                                · linarith only [h15246, h15611, hlam]
                              · linarith only [h14803, h15610, hlam]
                            · linarith only [h11558, h15609, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h15483, hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15618 | h15618
                        · linarith only [h10058, h15618, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15620 | h15620
                          · linarith only [h14803, h15620, hlam]
                          · rcases p15564_3 (m.d 0 3) (by simp) with h15622 | h15622
                            · rcases p15564_3 (m.d 0 4) (by simp) with h15623 | h15623
                              · rcases p15564_3 (m.d 0 5) (by simp) with h15624 | h15624
                                · linarith only [h15485, h15624, hlam]
                                · rcases h0emin with h15626 | h15626 | h15626 | h15626 | h15626
                                  · linarith only [h0, h15246, h15626, hlam, p15564_1, u0elo3]
                                  · linarith only [h15246, h15626, hlam, p15564_1, u0elo3]
                                  · rcases h2bigk with h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c | h15629c
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, hlam, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h11558, hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h14803, hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h15246, hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, h15486, hc01, hc23, hlam, hphi, ht12, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h15486, hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h15554, hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h15556, hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      rcases p15629_3 (m.d 0 2) (by simp) with h15640 | h15640
                                      · linarith only [h15640, hlam, p15629_0]
                                      · rcases p15629_3 (m.d 1 2) (by simp) with h15642 | h15642
                                        · linarith only [h15486, h15642, hlam]
                                        · linarith only [h0, h15642, hlam]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      rcases p15629_3 (m.d 0 2) (by simp) with h15649 | h15649
                                      · linarith only [h15649, hlam, p15629_0]
                                      · rcases p15629_3 (m.d 1 2) (by simp) with h15651 | h15651
                                        · linarith only [h15554, h15651, hlam]
                                        · linarith only [h0, h15651, hlam]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h15560, hlam, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      rcases p15629_3 (m.d 0 2) (by simp) with h15658 | h15658
                                      · linarith only [h15658, hlam, p15629_0]
                                      · rcases p15629_3 (m.d 1 2) (by simp) with h15660 | h15660
                                        · linarith only [h15556, h15660, hlam]
                                        · linarith only [h0, h15660, hlam]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h15561, hlam, p15629_1]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [h15562, hlam, p15629_0]
                                    · have p15629_0 := h15629c.1
                                      have p15629_1 := h15629c.2.1
                                      have p15629_2 := h15629c.2.2.1
                                      have p15629_3 := h15629c.2.2.2
                                      linarith only [hlam, p15629_0]
                                  · rcases h2bigk with h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c | h15667c
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, hlam, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h11558, hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h14803, hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h15246, hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, h15486, hc01, hc23, hlam, hphi, ht12, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h15486, hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h15554, hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h15556, hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      rcases p15667_3 (m.d 0 2) (by simp) with h15678 | h15678
                                      · linarith only [h15678, hlam, p15667_0]
                                      · rcases p15667_3 (m.d 1 2) (by simp) with h15680 | h15680
                                        · linarith only [h15486, h15680, hlam]
                                        · linarith only [h0, h15680, hlam]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      rcases p15667_3 (m.d 0 2) (by simp) with h15687 | h15687
                                      · linarith only [h15687, hlam, p15667_0]
                                      · rcases p15667_3 (m.d 1 2) (by simp) with h15689 | h15689
                                        · linarith only [h15554, h15689, hlam]
                                        · linarith only [h0, h15689, hlam]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h15560, hlam, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      rcases p15667_3 (m.d 0 2) (by simp) with h15696 | h15696
                                      · linarith only [h15696, hlam, p15667_0]
                                      · rcases p15667_3 (m.d 1 2) (by simp) with h15698 | h15698
                                        · linarith only [h15556, h15698, hlam]
                                        · linarith only [h0, h15698, hlam]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h15561, hlam, p15667_1]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [h15562, hlam, p15667_0]
                                    · have p15667_0 := h15667c.1
                                      have p15667_1 := h15667c.2.1
                                      have p15667_2 := h15667c.2.2.1
                                      have p15667_3 := h15667c.2.2.2
                                      linarith only [hlam, p15667_0]
                                  · linarith only [h15483, h15626, hlam, p15564_1, u0elo2]
                              · linarith only [h15485, h15623, hlam]
                            · linarith only [h15484, h15622, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15708 | h15708
                        · linarith only [h11024, h15708, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15710 | h15710
                          · linarith only [h15246, h15710, hlam]
                          · linarith only [h0, h15710, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        rcases p15564_3 (m.d 0 1) (by simp) with h15713 | h15713
                        · linarith only [h11024, h15713, hlam]
                        · rcases p15564_3 (m.d 0 2) (by simp) with h15715 | h15715
                          · linarith only [h15246, h15715, hlam]
                          · rcases p15564_3 (m.d 0 3) (by simp) with h15717 | h15717
                            · rcases p15564_3 (m.d 0 4) (by simp) with h15718 | h15718
                              · rcases p15564_3 (m.d 0 5) (by simp) with h15719 | h15719
                                · rcases h0emin with h15720 | h15720 | h15720 | h15720 | h15720
                                  · linarith only [h0, h15720, hlam, p15564_1, u0elo4]
                                  · linarith only [h15720, hlam, p15564_1, u0elo4]
                                  · rcases h2bigk with h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c | h15723c
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, hlam, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h11558, hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h14803, hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h15246, hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, h15486, hc01, hc23, hlam, hphi, ht12, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h15486, hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h15554, hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h15556, hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      rcases p15723_3 (m.d 0 2) (by simp) with h15734 | h15734
                                      · linarith only [h15734, hlam, p15723_0]
                                      · rcases p15723_3 (m.d 1 2) (by simp) with h15736 | h15736
                                        · linarith only [h15486, h15736, hlam]
                                        · linarith only [h0, h15736, hlam]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      rcases p15723_3 (m.d 0 2) (by simp) with h15743 | h15743
                                      · linarith only [h15743, hlam, p15723_0]
                                      · rcases p15723_3 (m.d 1 2) (by simp) with h15745 | h15745
                                        · linarith only [h15554, h15745, hlam]
                                        · linarith only [h0, h15745, hlam]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h15560, hlam, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, h11024, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15564_1, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      rcases p15723_3 (m.d 0 2) (by simp) with h15752 | h15752
                                      · linarith only [h15752, hlam, p15723_0]
                                      · rcases p15723_3 (m.d 1 2) (by simp) with h15754 | h15754
                                        · linarith only [h15556, h15754, hlam]
                                        · linarith only [h0, h15754, hlam]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h15561, hlam, p15723_1]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [h15562, hlam, p15723_0]
                                    · have p15723_0 := h15723c.1
                                      have p15723_1 := h15723c.2.1
                                      have p15723_2 := h15723c.2.2.1
                                      have p15723_3 := h15723c.2.2.2
                                      linarith only [hlam, p15723_0]
                                  · rcases h2bigk with h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c | h15761c
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, hlam, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h11558, hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h14803, hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h15246, hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, h15486, hc01, hc23, hlam, hphi, ht12, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h15486, hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h15554, hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h15556, hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      rcases p15761_3 (m.d 0 2) (by simp) with h15772 | h15772
                                      · linarith only [h15772, hlam, p15761_0]
                                      · rcases p15761_3 (m.d 1 2) (by simp) with h15774 | h15774
                                        · linarith only [h15486, h15774, hlam]
                                        · linarith only [h0, h15774, hlam]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      rcases p15761_3 (m.d 0 2) (by simp) with h15781 | h15781
                                      · linarith only [h15781, hlam, p15761_0]
                                      · rcases p15761_3 (m.d 1 2) (by simp) with h15783 | h15783
                                        · linarith only [h15554, h15783, hlam]
                                        · linarith only [h0, h15783, hlam]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h15560, hlam, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, h11024, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15564_1, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      rcases p15761_3 (m.d 0 2) (by simp) with h15790 | h15790
                                      · linarith only [h15790, hlam, p15761_0]
                                      · rcases p15761_3 (m.d 1 2) (by simp) with h15792 | h15792
                                        · linarith only [h15556, h15792, hlam]
                                        · linarith only [h0, h15792, hlam]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h15561, hlam, p15761_1]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [h15562, hlam, p15761_0]
                                    · have p15761_0 := h15761c.1
                                      have p15761_1 := h15761c.2.1
                                      have p15761_2 := h15761c.2.2.1
                                      have p15761_3 := h15761c.2.2.2
                                      linarith only [hlam, p15761_0]
                                  · rcases h2bigk with h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c | h15799c
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, hlam, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h11558, hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h14803, hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h15246, hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, h15486, hc01, hc23, hlam, hphi, ht12, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h15486, hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h15554, hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h15556, hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      rcases p15799_3 (m.d 0 2) (by simp) with h15810 | h15810
                                      · linarith only [h15810, hlam, p15799_0]
                                      · rcases p15799_3 (m.d 1 2) (by simp) with h15812 | h15812
                                        · linarith only [h15486, h15812, hlam]
                                        · linarith only [h0, h15812, hlam]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      rcases p15799_3 (m.d 0 2) (by simp) with h15819 | h15819
                                      · linarith only [h15819, hlam, p15799_0]
                                      · rcases p15799_3 (m.d 1 2) (by simp) with h15821 | h15821
                                        · linarith only [h15554, h15821, hlam]
                                        · linarith only [h0, h15821, hlam]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h15560, hlam, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, h11024, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15564_1, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      rcases p15799_3 (m.d 0 2) (by simp) with h15828 | h15828
                                      · linarith only [h15828, hlam, p15799_0]
                                      · rcases p15799_3 (m.d 1 2) (by simp) with h15830 | h15830
                                        · linarith only [h15556, h15830, hlam]
                                        · linarith only [h0, h15830, hlam]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h15561, hlam, p15799_1]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [h15562, hlam, p15799_0]
                                    · have p15799_0 := h15799c.1
                                      have p15799_1 := h15799c.2.1
                                      have p15799_2 := h15799c.2.2.1
                                      have p15799_3 := h15799c.2.2.2
                                      linarith only [hlam, p15799_0]
                                · linarith only [h15246, h15719, hlam]
                              · linarith only [h14803, h15718, hlam]
                            · linarith only [h11558, h15717, hlam]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h15484, hlam, p15564_0]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [h15485, hlam, p15564_1]
                      · have p15564_0 := h15564c.1
                        have p15564_1 := h15564c.2.1
                        have p15564_2 := h15564c.2.2.1
                        have p15564_3 := h15564c.2.2.2
                        linarith only [hlam, p15564_0]
                    · rcases h0bigk with h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c | h15843c
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h0, hlam, p15843_1]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h6793, hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h10058, hlam, p15843_1]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h11024, hlam, p15843_1]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h11558, hc01, hc23, hlam, hphi, ht12, p15843_1]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h11558, hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h14803, hlam, p15843_1]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h15246, hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        rcases p15843_3 (m.d 0 1) (by simp) with h15854 | h15854
                        · linarith only [h15854, h6793, hlam]
                        · rcases p15843_3 (m.d 0 2) (by simp) with h15856 | h15856
                          · linarith only [h11558, h15856, hlam]
                          · linarith only [h0, h15856, hlam]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        rcases p15843_3 (m.d 0 1) (by simp) with h15859 | h15859
                        · linarith only [h15859, h6793, hlam]
                        · rcases p15843_3 (m.d 0 2) (by simp) with h15861 | h15861
                          · linarith only [h11558, h15861, hlam]
                          · rcases p15843_3 (m.d 0 3) (by simp) with h15863 | h15863
                            · rcases p15843_3 (m.d 0 4) (by simp) with h15864 | h15864
                              · linarith only [h15483, h15864, hlam]
                              · linarith only [h14803, h15864, hlam]
                            · linarith only [h11558, h15863, hlam]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h15485, h15563, hc34, hlam, hphi, ht0b, ht45, ht5b, p15843_1, u0elo2]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h15485, h15563, hc34, hlam, hphi, ht0b, ht45, ht5b, p15843_1, u0elo2]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        rcases p15843_3 (m.d 0 1) (by simp) with h15871 | h15871
                        · linarith only [h10058, h15871, hlam]
                        · rcases p15843_3 (m.d 0 2) (by simp) with h15873 | h15873
                          · linarith only [h14803, h15873, hlam]
                          · linarith only [h0, h15873, hlam]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        rcases p15843_3 (m.d 0 1) (by simp) with h15876 | h15876
                        · linarith only [h10058, h15876, hlam]
                        · rcases p15843_3 (m.d 0 2) (by simp) with h15878 | h15878
                          · linarith only [h14803, h15878, hlam]
                          · rcases p15843_3 (m.d 0 3) (by simp) with h15880 | h15880
                            · rcases p15843_3 (m.d 0 4) (by simp) with h15881 | h15881
                              · rcases p15843_3 (m.d 0 5) (by simp) with h15882 | h15882
                                · linarith only [h15485, h15882, hlam]
                                · linarith only [h15246, h15882, hlam]
                              · linarith only [h14803, h15881, hlam]
                            · linarith only [h11558, h15880, hlam]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h15483, hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h15485, h15563, hc34, hlam, hphi, ht0b, ht45, ht5b, p15843_1, u0elo3]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        rcases p15843_3 (m.d 0 1) (by simp) with h15890 | h15890
                        · linarith only [h11024, h15890, hlam]
                        · rcases p15843_3 (m.d 0 2) (by simp) with h15892 | h15892
                          · linarith only [h15246, h15892, hlam]
                          · linarith only [h0, h15892, hlam]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        rcases p15843_3 (m.d 0 1) (by simp) with h15895 | h15895
                        · linarith only [h11024, h15895, hlam]
                        · rcases p15843_3 (m.d 0 2) (by simp) with h15897 | h15897
                          · linarith only [h15246, h15897, hlam]
                          · rcases p15843_3 (m.d 0 3) (by simp) with h15899 | h15899
                            · rcases p15843_3 (m.d 0 4) (by simp) with h15900 | h15900
                              · rcases p15843_3 (m.d 0 5) (by simp) with h15901 | h15901
                                · rcases h0emin with h15902 | h15902 | h15902 | h15902 | h15902
                                  · linarith only [h0, h15902, hlam, p15843_1, u0elo4]
                                  · linarith only [h15902, hlam, p15843_1, u0elo4]
                                  · rcases h2bigk with h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c | h15905c
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h0, hlam, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h11558, hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h14803, hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h15246, hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h0, h15556, h15560, h15562, hc01, hc23, hlam, hphi, ht12, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h15486, hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h15554, hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h15556, hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      rcases p15905_3 (m.d 0 2) (by simp) with h15916 | h15916
                                      · linarith only [h15916, hlam, p15905_0]
                                      · rcases p15905_3 (m.d 1 2) (by simp) with h15918 | h15918
                                        · linarith only [h15486, h15918, hlam]
                                        · linarith only [h0, h15918, hlam]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      rcases p15905_3 (m.d 0 2) (by simp) with h15925 | h15925
                                      · linarith only [h15925, hlam, p15905_0]
                                      · rcases p15905_3 (m.d 1 2) (by simp) with h15927 | h15927
                                        · linarith only [h15554, h15927, hlam]
                                        · linarith only [h0, h15927, hlam]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h15560, hlam, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h11024, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      rcases p15905_3 (m.d 0 2) (by simp) with h15934 | h15934
                                      · linarith only [h15934, hlam, p15905_0]
                                      · rcases p15905_3 (m.d 1 2) (by simp) with h15936 | h15936
                                        · linarith only [h15556, h15936, hlam]
                                        · linarith only [h0, h15936, hlam]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h15561, hlam, p15905_1]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [h15562, hlam, p15905_0]
                                    · have p15905_0 := h15905c.1
                                      have p15905_1 := h15905c.2.1
                                      have p15905_2 := h15905c.2.2.1
                                      have p15905_3 := h15905c.2.2.2
                                      linarith only [hlam, p15905_0]
                                  · rcases h2bigk with h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c | h15943c
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, hlam, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h11558, hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h14803, hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h15246, hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, h15486, hc01, hc23, hlam, hphi, ht12, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h15486, hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h15554, hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h15556, hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      rcases p15943_3 (m.d 0 2) (by simp) with h15954 | h15954
                                      · linarith only [h15954, hlam, p15943_0]
                                      · rcases p15943_3 (m.d 1 2) (by simp) with h15956 | h15956
                                        · linarith only [h15486, h15956, hlam]
                                        · linarith only [h0, h15956, hlam]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      rcases p15943_3 (m.d 0 2) (by simp) with h15963 | h15963
                                      · linarith only [h15963, hlam, p15943_0]
                                      · rcases p15943_3 (m.d 1 2) (by simp) with h15965 | h15965
                                        · linarith only [h15554, h15965, hlam]
                                        · linarith only [h0, h15965, hlam]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h15560, hlam, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, h11024, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15843_1, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      rcases p15943_3 (m.d 0 2) (by simp) with h15972 | h15972
                                      · linarith only [h15972, hlam, p15943_0]
                                      · rcases p15943_3 (m.d 1 2) (by simp) with h15974 | h15974
                                        · linarith only [h15556, h15974, hlam]
                                        · linarith only [h0, h15974, hlam]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h15561, hlam, p15943_1]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [h15562, hlam, p15943_0]
                                    · have p15943_0 := h15943c.1
                                      have p15943_1 := h15943c.2.1
                                      have p15943_2 := h15943c.2.2.1
                                      have p15943_3 := h15943c.2.2.2
                                      linarith only [hlam, p15943_0]
                                  · rcases h2bigk with h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c | h15981c
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, hlam, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h11558, hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h14803, hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h15246, hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, h15486, hc01, hc23, hlam, hphi, ht12, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h15486, hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h15554, hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h15556, hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      rcases p15981_3 (m.d 0 2) (by simp) with h15992 | h15992
                                      · linarith only [h15992, hlam, p15981_0]
                                      · rcases p15981_3 (m.d 1 2) (by simp) with h15994 | h15994
                                        · linarith only [h15486, h15994, hlam]
                                        · linarith only [h0, h15994, hlam]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, h15246, hc01, hc23, hlam, hphi, ht12, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      rcases p15981_3 (m.d 0 2) (by simp) with h16001 | h16001
                                      · linarith only [h16001, hlam, p15981_0]
                                      · rcases p15981_3 (m.d 1 2) (by simp) with h16003 | h16003
                                        · linarith only [h15554, h16003, hlam]
                                        · linarith only [h0, h16003, hlam]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h15560, hlam, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, h11024, h15556, h15560, hc01, hc23, hlam, hphi, ht12, p15843_1, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      rcases p15981_3 (m.d 0 2) (by simp) with h16010 | h16010
                                      · linarith only [h16010, hlam, p15981_0]
                                      · rcases p15981_3 (m.d 1 2) (by simp) with h16012 | h16012
                                        · linarith only [h15556, h16012, hlam]
                                        · linarith only [h0, h16012, hlam]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h15561, hlam, p15981_1]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [h15562, hlam, p15981_0]
                                    · have p15981_0 := h15981c.1
                                      have p15981_1 := h15981c.2.1
                                      have p15981_2 := h15981c.2.2.1
                                      have p15981_3 := h15981c.2.2.2
                                      linarith only [hlam, p15981_0]
                                · linarith only [h15246, h15901, hlam]
                              · linarith only [h14803, h15900, hlam]
                            · linarith only [h11558, h15899, hlam]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h15484, hlam, p15843_0]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [h15485, hlam, p15843_1]
                      · have p15843_0 := h15843c.1
                        have p15843_1 := h15843c.2.1
                        have p15843_2 := h15843c.2.2.1
                        have p15843_3 := h15843c.2.2.2
                        linarith only [hlam, p15843_0]
                  · linarith only [h14803, h15485, h15562, hlam]
                · linarith only [h15484, h15486, h15561, h6793, hlam]
              · linarith only [h15483, h15486, h15560, h6793, hlam]
            · linarith only [h10058, h15485, h15559, hlam]
          · linarith only [h15483, h15558, h6793, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h16030 | h16030
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16031 | h16031
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16032 | h16032
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16033 | h16033
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16034 | h16034
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16035 | h16035
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16036 | h16036
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16037 | h16037
                  · linarith only [h0, h14803, h15485, h16030, h16035, h16037, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14803, h16030, h16033, h16034, h16037, hc01, hc12, hlam, hphi]
                · linarith only [h11558, h15484, h16036, hlam]
              · linarith only [h11558, h15483, h16035, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16042 | h16042
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16043 | h16043
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16044 | h16044
                  · linarith only [h16031, h16034, h16044, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16046 | h16046
                    · linarith only [h14803, h15483, h16031, h16034, h16046, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c | h16048c
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h0, hlam, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h6793, hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h10058, hlam, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h11024, hlam, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h14803, h16031, hc01, hc14, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h11558, hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h14803, hlam, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h15246, hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h11558, h16030, hc01, hc12, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h0, h11558, h16030, hc01, hc12, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h0, h11558, h14803, h16030, hc01, hc12, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h0, h11558, h14803, h15485, h16030, hc01, hc12, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h10058, h16034, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h0, h14803, h16031, h16034, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h15483, hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h15485, hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h11558, h15484, h16030, hc01, hc12, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h0, h11558, h15484, h16030, hc01, hc12, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h15484, hlam, p16048_0]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [h10058, h11558, h15484, h16030, hc01, hc12, hlam, hphi, p16048_1]
                      · have p16048_0 := h16048c.1
                        have p16048_1 := h16048c.2.1
                        have p16048_2 := h16048c.2.2.1
                        have p16048_3 := h16048c.2.2.2
                        linarith only [hlam, p16048_0]
                · linarith only [h11558, h15484, h16043, hlam]
              · linarith only [h0, h10058, h11558, h15483, h16034, h16042, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h11558, h15483, h16030, h16033, hlam]
        · linarith only [h0, h11558, h16030, h16032, hc01, hc25, hlam, hphi, ht12]
      · linarith only [h0, h11558, h16030, h16031, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16079 | h16079
      · linarith only [h0, h14803, h16030, h16079, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16081 | h16081
        · linarith only [h0, h15246, h16030, h16081, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16083 | h16083
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16084 | h16084
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16085 | h16085
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16086 | h16086
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16087 | h16087
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16088 | h16088
                    · linarith only [h15483, h15485, h16088, hlam]
                    · rcases h0bigk with h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c | h16090c
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h0, hlam, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h6793, hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h10058, hlam, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h11024, hlam, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h0, h16081, h16085, h16087, hc01, hc23, hlam, hphi, ht12, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h11558, hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h14803, hlam, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h15246, hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        rcases p16090_3 (m.d 0 1) (by simp) with h16101 | h16101
                        · linarith only [h16101, h6793, hlam]
                        · rcases p16090_3 (m.d 0 2) (by simp) with h16103 | h16103
                          · linarith only [h11558, h16103, hlam]
                          · linarith only [h0, h16103, hlam]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        rcases p16090_3 (m.d 0 1) (by simp) with h16106 | h16106
                        · linarith only [h16106, h6793, hlam]
                        · rcases p16090_3 (m.d 0 2) (by simp) with h16108 | h16108
                          · linarith only [h11558, h16108, hlam]
                          · rcases p16090_3 (m.d 0 3) (by simp) with h16110 | h16110
                            · rcases p16090_3 (m.d 0 4) (by simp) with h16111 | h16111
                              · linarith only [h15483, h16111, hlam]
                              · linarith only [h14803, h16111, hlam]
                            · linarith only [h11558, h16110, hlam]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        rcases p16090_3 (m.d 0 1) (by simp) with h16116 | h16116
                        · linarith only [h16116, h6793, hlam]
                        · rcases p16090_3 (m.d 0 2) (by simp) with h16118 | h16118
                          · linarith only [h11558, h16118, hlam]
                          · rcases p16090_3 (m.d 0 3) (by simp) with h16120 | h16120
                            · rcases p16090_3 (m.d 0 4) (by simp) with h16121 | h16121
                              · linarith only [h15483, h16121, hlam]
                              · rcases p16090_3 (m.d 0 5) (by simp) with h16123 | h16123
                                · linarith only [h15484, h16123, hlam]
                                · linarith only [h15485, h16123, hlam]
                            · linarith only [h15483, h16120, hlam]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        rcases p16090_3 (m.d 0 1) (by simp) with h16127 | h16127
                        · linarith only [h16127, h6793, hlam]
                        · rcases p16090_3 (m.d 0 2) (by simp) with h16129 | h16129
                          · linarith only [h11558, h16129, hlam]
                          · rcases p16090_3 (m.d 0 3) (by simp) with h16131 | h16131
                            · rcases p16090_3 (m.d 0 4) (by simp) with h16132 | h16132
                              · linarith only [h15483, h16132, hlam]
                              · rcases p16090_3 (m.d 0 5) (by simp) with h16134 | h16134
                                · linarith only [h15484, h16134, hlam]
                                · rcases h0emin with h16136 | h16136 | h16136 | h16136 | h16136
                                  · linarith only [h0, h16081, h16085, h16087, h16136, hc23, hlam, ht01, ht12]
                                  · linarith only [h14803, h15485, h16136, hlam, p16090_1, u0elo2]
                                  · rcases h2bigk with h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, hlam, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h11558, hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h14803, hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h15246, hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, h16081, h16085, h16087, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h16030, hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h16079, hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h16081, hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      rcases p16139_3 (m.d 0 2) (by simp) with h16150 | h16150
                                      · linarith only [h16150, hlam, p16139_0]
                                      · rcases p16139_3 (m.d 1 2) (by simp) with h16152 | h16152
                                        · linarith only [h16030, h16152, hlam]
                                        · linarith only [h0, h16152, hlam]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, h14803, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, h16081, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      rcases p16139_3 (m.d 0 2) (by simp) with h16159 | h16159
                                      · linarith only [h16159, hlam, p16139_0]
                                      · rcases p16139_3 (m.d 1 2) (by simp) with h16161 | h16161
                                        · linarith only [h16079, h16161, hlam]
                                        · linarith only [h0, h16161, hlam]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h16085, hlam, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, h16081, h16085, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      rcases p16139_3 (m.d 0 2) (by simp) with h16168 | h16168
                                      · linarith only [h16168, hlam, p16139_0]
                                      · rcases p16139_3 (m.d 1 2) (by simp) with h16170 | h16170
                                        · linarith only [h16081, h16170, hlam]
                                        · linarith only [h0, h16170, hlam]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h16086, hlam, p16139_1]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [h16087, hlam, p16139_0]
                                    · have p16139_0 := h16139c.1
                                      have p16139_1 := h16139c.2.1
                                      have p16139_2 := h16139c.2.2.1
                                      have p16139_3 := h16139c.2.2.2
                                      linarith only [hlam, p16139_0]
                                  · linarith only [h15485, h16136, hlam, p16090_1, u0elo2]
                                  · linarith only [h16136, hlam, p16090_1, u0elo2]
                            · linarith only [h15484, h16131, hlam]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h15485, h16030, h16083, h16084, hc01, hc23, hlam, hphi, ht12, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h0, h15485, h16030, h16083, h16084, hc01, hc23, hlam, hphi, ht12, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h15483, hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h15485, hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h15485, h16030, h16083, h16084, hc01, hc23, hlam, hphi, ht12, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h0, h15485, h16030, h16083, h16084, hc01, hc23, hlam, hphi, ht12, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h15484, hlam, p16090_0]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [h10058, h15485, h16030, h16083, h16084, hc01, hc23, hlam, hphi, ht12, p16090_1]
                      · have p16090_0 := h16090c.1
                        have p16090_1 := h16090c.2.1
                        have p16090_2 := h16090c.2.2.1
                        have p16090_3 := h16090c.2.2.2
                        linarith only [hlam, p16090_0]
                  · linarith only [h0, h14803, h16030, h16083, h16084, h16087, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h15484, h15485, h16030, h16083, h16084, h16086, hc05, hlam, hphi, ht0b, ht5b, u0elo2]
              · linarith only [h15483, h15485, h16030, h16083, h16084, h16085, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16193 | h16193
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16194 | h16194
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16195 | h16195
                  · linarith only [h10058, h16084, h16193, h16195, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h16079, h16195, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h11558, h15484, h16194, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h10058, h15483, h16030, h16084, h16193, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h15483, h16083, h6793, hlam]

end R2N4
