import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_23_L_0_H_I_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0elo := hb0.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h560 | h560
  · rcases m.htr 1 2 3 (by decide) (by decide) with h561 | h561
    · rcases m.htr 1 3 4 (by decide) (by decide) with h562 | h562
      · rcases m.htr 1 3 5 (by decide) (by decide) with h563 | h563
        · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
          · rcases m.htr 2 3 5 (by decide) (by decide) with h565 | h565
            · rcases m.htr 3 4 5 (by decide) (by decide) with h566 | h566
              · rcases h3bigk with h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h0, hlam, p567_1]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p567_1, u0elo2]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h566, hc45, hlam, hphi, ht0b, ht5b, p567_1, u0elo2]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p567_1, u0elo2]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h0, h561, hc01, hc12, hlam, hphi, p567_1]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h561, h564, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h561, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  rcases p567_3 (m.d 0 3) (by simp) with h577 | h577
                  · linarith only [h0, h577, hlam]
                  · linarith only [h560, h577, hlam]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h559, h566, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p567_1]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h561, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h561, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h561, h566, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p567_1]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h559, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h562, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h564, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h559, h566, hc45, hlam, hphi, ht0b, ht5b, p567_1, u0elo2]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h560, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h563, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h565, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [h566, hlam, p567_0]
                · have p567_0 := h567c.1
                  have p567_1 := h567c.2.1
                  have p567_2 := h567c.2.2.1
                  have p567_3 := h567c.2.2.2
                  linarith only [hlam, p567_0]
              · rcases h3bigk with h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c | h595c
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h0, hlam, p595_1]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p595_1, u0elo2]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p595_1, u0elo2]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h566, hc34, hlam, hphi, ht0b, ht45, ht5b, p595_1, u0elo2]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h0, h561, hc01, hc12, hlam, hphi, p595_1]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h561, h565, h566, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p595_1]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  rcases p595_3 (m.d 0 3) (by simp) with h604 | h604
                  · linarith only [h0, h604, hlam]
                  · linarith only [h559, h604, hlam]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  rcases p595_3 (m.d 0 3) (by simp) with h607 | h607
                  · linarith only [h0, h607, hlam]
                  · linarith only [h560, h607, hlam]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h560, h566, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p595_1]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h561, hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h561, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p595_1]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h561, h566, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p595_1]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h559, hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h562, hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h564, hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h566, hlam, p595_1]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h560, hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h563, hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h565, hlam, p595_0]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [h560, hc34, hlam, hphi, ht0b, ht45, ht5b, p595_1, u0elo2]
                · have p595_0 := h595c.1
                  have p595_1 := h595c.2.1
                  have p595_2 := h595c.2.2.1
                  have p595_3 := h595c.2.2.2
                  linarith only [hlam, p595_0]
            · linarith only [h560, h564, h565, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h626 | h626
            · linarith only [h559, h564, h626, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
              · rcases h3bigk with h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h0, hlam, p629_1]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p629_1, u0elo2]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h626, h628, hc25, hlam, hphi, ht0b, ht5b, p629_1, u0elo2]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h626, hc25, hlam, hphi, ht0b, ht5b, p629_1, u0elo2]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h0, h561, hc01, hc12, hlam, hphi, p629_1]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  rcases p629_3 (m.d 0 3) (by simp) with h637 | h637
                  · linarith only [h0, h637, hlam]
                  · linarith only [h559, h626, h628, h637, hlam]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h561, h626, h628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p629_1]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h561, h626, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p629_1]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h559, h626, h628, hlam, p629_1]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h561, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h564, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h626, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h559, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h562, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p629_1, u0elo2]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h559, h626, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p629_1, u0elo2]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h560, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h563, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [hc23, hc35, hlam, hphi, p629_1]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [h628, hlam, p629_0]
                · have p629_0 := h629c.1
                  have p629_1 := h629c.2.1
                  have p629_2 := h629c.2.2.1
                  have p629_3 := h629c.2.2.2
                  linarith only [hlam, p629_0]
              · rcases h3bigk with h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h0, hlam, p657_1]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p657_1, u0elo2]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p657_1, u0elo2]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p657_1, u0elo2]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h0, h561, hc01, hc12, hlam, hphi, p657_1]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  rcases p657_3 (m.d 0 3) (by simp) with h665 | h665
                  · linarith only [h0, h665, hlam]
                  · linarith only [h560, h564, h628, h665, hlam]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h561, h564, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p657_1]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h561, h564, h628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p657_1]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h560, h564, h628, hlam, p657_1]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h561, hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h564, hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h626, hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h559, hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h562, hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h560, h628, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p657_1, u0elo2]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h628, hlam, p657_1]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h560, hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h563, hlam, p657_0]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p657_1, u0elo2]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [h560, hc34, hlam, hphi, ht0b, ht45, ht5b, p657_1, u0elo2]
                · have p657_0 := h657c.1
                  have p657_1 := h657c.2.1
                  have p657_2 := h657c.2.2.1
                  have p657_3 := h657c.2.2.2
                  linarith only [hlam, p657_0]
        · linarith only [h0, h560, h563, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
      · linarith only [h0, h559, h562, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
      · rcases m.htr 1 3 5 (by decide) (by decide) with h688 | h688
        · rcases m.htr 2 3 4 (by decide) (by decide) with h689 | h689
          · rcases m.htr 2 3 5 (by decide) (by decide) with h690 | h690
            · rcases m.htr 3 4 5 (by decide) (by decide) with h691 | h691
              · rcases h3bigk with h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, h561, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p692_1, u0elo2]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p692_1, u0elo2]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, h561, hc01, hc23, hlam, hphi, ht12, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h561, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h561, h691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  rcases p692_3 (m.d 0 3) (by simp) with h702 | h702
                  · linarith only [h0, h702, hlam]
                  · linarith only [h560, h702, hlam]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h559, h691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  rcases p692_3 (m.d 0 3) (by simp) with h709 | h709
                  · linarith only [h0, h561, h709, hlam]
                  · linarith only [h560, h709, hlam]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h559, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h687, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h689, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h559, h691, hc45, hlam, hphi, ht0b, ht5b, p692_1, u0elo2]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h560, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h688, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h690, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h691, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
              · rcases h3bigk with h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h0, hlam, p722_1]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h561, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p722_1, u0elo2]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1, u0elo2]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p722_1, u0elo2]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h0, h561, hc01, hc23, hlam, hphi, ht12, p722_1]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h561, hlam, p722_1]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  rcases p722_3 (m.d 0 3) (by simp) with h731 | h731
                  · linarith only [h0, h731, hlam]
                  · linarith only [h559, h731, hlam]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  rcases p722_3 (m.d 0 3) (by simp) with h734 | h734
                  · linarith only [h0, h734, hlam]
                  · linarith only [h560, h734, hlam]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h560, h691, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p722_1]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p722_1]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  rcases p722_3 (m.d 0 3) (by simp) with h740 | h740
                  · linarith only [h0, h561, h740, hlam]
                  · linarith only [h559, h740, hlam]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  rcases p722_3 (m.d 0 3) (by simp) with h743 | h743
                  · linarith only [h691, h743, hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1, u0elo2]
                  · linarith only [h560, h743, hlam]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h559, hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h687, hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h689, hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h691, hlam, p722_1]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h560, hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h688, hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h690, hlam, p722_0]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [h560, hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1, u0elo2]
                · have p722_0 := h722c.1
                  have p722_1 := h722c.2.1
                  have p722_2 := h722c.2.2.1
                  have p722_3 := h722c.2.2.2
                  linarith only [hlam, p722_0]
            · linarith only [h560, h561, h690, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h0, h559, h561, h689, hlam]
        · linarith only [h0, h560, h688, hlam]
      · linarith only [h0, h559, h687, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
    · rcases m.htr 1 3 4 (by decide) (by decide) with h761 | h761
      · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
        · rcases m.htr 2 3 4 (by decide) (by decide) with h763 | h763
          · rcases m.htr 2 3 5 (by decide) (by decide) with h764 | h764
            · linarith only [h559, h560, h760, h764, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h766 | h766
              · linarith only [h559, h560, h762, h766, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
              · rcases h3bigk with h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h0, hlam, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h560, h760, h762, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h560, h760, h762, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h560, hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h0, h760, hc01, hc12, hlam, hphi, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h760, h763, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  rcases p768_3 (m.d 0 3) (by simp) with h777 | h777
                  · linarith only [h0, h777, hlam]
                  · linarith only [h559, h777, hlam]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h559, h560, h760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h559, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h760, hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h764, hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h559, hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h761, hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h763, hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h766, hlam, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h559, h762, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h762, hlam, p768_0]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h760, h762, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [h760, h762, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1]
                · have p768_0 := h768c.1
                  have p768_1 := h768c.2.1
                  have p768_2 := h768c.2.2.1
                  have p768_3 := h768c.2.2.2
                  linarith only [hlam, p768_0]
          · linarith only [h559, h560, h760, h762, h763, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h797 | h797
          · rcases m.htr 2 3 5 (by decide) (by decide) with h798 | h798
            · linarith only [h0, h762, h798, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h800 | h800
              · linarith only [h0, h559, h762, h800, hlam]
              · rcases h3bigk with h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c | h802c
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h0, hlam, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h0, h762, h800, hc23, hc45, hlam, hphi, ht34, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h0, h762, h800, hc34, hc45, hlam, hphi, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h560, hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h762, h800, hc03, hc45, hlam, hphi, ht34, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h762, h800, hc23, hc45, hlam, hphi, ht34, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h762, h800, hc34, hc45, hlam, hphi, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h762, hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h559, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h760, hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h760, h762, h800, hc34, hc45, hlam, hphi, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h798, hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h559, hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h761, hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h797, hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [hlam, p802_0]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h800, hlam, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h559, h800, hc34, hc45, hlam, hphi, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h800, hc13, hc45, hlam, hphi, ht34, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h797, h800, hc34, hc45, hlam, hphi, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [h800, hc34, hc45, hlam, hphi, p802_1]
                · have p802_0 := h802c.1
                  have p802_1 := h802c.2.1
                  have p802_2 := h802c.2.2.1
                  have p802_3 := h802c.2.2.2
                  linarith only [hlam, p802_0]
          · linarith only [h559, h560, h797, hc23, hc35, hlam, hphi]
      · linarith only [h0, h559, h761, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
      · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
        · rcases m.htr 2 3 4 (by decide) (by decide) with h832 | h832
          · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
            · rcases m.htr 3 4 5 (by decide) (by decide) with h834 | h834
              · linarith only [h559, h560, h760, h831, h834, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases h3bigk with h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c | h836c
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h0, hlam, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h560, h760, h831, hlam, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h560, h760, h831, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h560, hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h0, h760, hc01, hc23, hlam, hphi, ht12, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h760, hlam, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  rcases p836_3 (m.d 0 3) (by simp) with h845 | h845
                  · linarith only [h0, h845, hlam]
                  · linarith only [h559, h845, hlam]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h559, h560, h760, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h559, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  rcases p836_3 (m.d 0 3) (by simp) with h852 | h852
                  · linarith only [h560, h760, h831, h852, hlam]
                  · linarith only [h559, h852, hlam]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h560, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h559, hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h830, hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h832, hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h834, hlam, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h831, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h831, hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h833, hlam, p836_0]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [h760, h831, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p836_1]
                · have p836_0 := h836c.1
                  have p836_1 := h836c.2.1
                  have p836_2 := h836c.2.2.1
                  have p836_3 := h836c.2.2.2
                  linarith only [hlam, p836_0]
            · linarith only [h760, h831, h833, hlam]
          · linarith only [h559, h560, h760, h831, h832, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h868 | h868
          · rcases m.htr 2 3 5 (by decide) (by decide) with h869 | h869
            · linarith only [h0, h831, h869, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h871 | h871
              · linarith only [h0, h559, h760, h869, h871, hlam]
              · rcases h3bigk with h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h0, hlam, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h0, h760, hlam, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h0, h760, h869, h871, hc34, hc45, hlam, hphi, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h560, hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h760, h869, h871, hc03, hc45, hlam, hphi, ht34, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h760, hlam, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h760, h869, h871, hc34, hc45, hlam, hphi, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h831, hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h559, h869, h871, hc34, hc45, hlam, hphi, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h869, h871, hc13, hc45, hlam, hphi, ht34, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h869, h871, hc34, hc45, hlam, hphi, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h869, hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h559, hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h830, hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h868, hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [hlam, p873_0]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h871, hlam, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h559, h871, hc34, hc45, hlam, hphi, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h0, h871, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h871, hc23, hc45, hlam, hphi, ht34, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [h871, hc34, hc45, hlam, hphi, p873_1]
                · have p873_0 := h873c.1
                  have p873_1 := h873c.2.1
                  have p873_2 := h873c.2.2.1
                  have p873_3 := h873c.2.2.2
                  linarith only [hlam, p873_0]
          · linarith only [h0, h559, h760, h868, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
      · linarith only [h0, h559, h830, hlam]

end R2N4
