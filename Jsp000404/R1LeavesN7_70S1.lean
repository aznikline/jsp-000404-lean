import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_70S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_0_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h516 | h516
  · rcases m.htr 0 3 5 (by decide) (by decide) with h517 | h517
    · rcases m.htr 0 4 5 (by decide) (by decide) with h518 | h518
      · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
        · rcases m.htr 2 3 4 (by decide) (by decide) with h520 | h520
          · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
            · rcases m.htr 2 4 5 (by decide) (by decide) with h522 | h522
              · rcases h5bigk with h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h0, hlam, p523_1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h517, hc25, hlam, hphi, ht0b, ht5b, p523_1, u0elo2]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h0, h519, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h0, h519, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h519, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h519, h521, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h519, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h519, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h516, hlam, p523_1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h516, hc15, hlam, hphi, ht0b, ht5b, p523_1, u0elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h516, hc35, hlam, hphi, ht0b, ht5b, p523_1, u0elo1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h516, hc45, hlam, hphi, ht0b, ht5b, p523_1, u0elo4]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h517, hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h519, hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h521, hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo4]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h518, hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p523_1]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h522, hlam, p523_0]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [h520, h522, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p523_1, u3elo2]
                · have p523_0 := h523c.1
                  have p523_1 := h523c.2.1
                  have p523_2 := h523c.2.2.1
                  have p523_3 := h523c.2.2.2
                  linarith only [hlam, p523_0]
              · rcases h5bigk with h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h0, hlam, p549_1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h0, h519, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p549_1, u3elo1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h0, h519, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p549_1, u3elo1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h0, h519, h520, h522, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p549_1, u3elo1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h519, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p549_1, u3elo1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h519, h520, h522, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p549_1, u3elo1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h519, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p549_1, u3elo1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h519, h520, h522, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p549_1, u3elo1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h516, hlam, p549_1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p549_1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h516, hc35, hlam, hphi, ht0b, ht5b, p549_1, u0elo4]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h522, hlam, p549_1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h517, hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h519, hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h521, hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h522, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p549_1, u3elo4]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h518, hlam, p549_0]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p549_1]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h518, h520, h522, hc34, hlam, hphi, ht0b, ht45, ht5b, p549_1, u0elo4]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [h518, hc35, hlam, hphi, ht0b, ht5b, p549_1, u0elo3]
                · have p549_0 := h549c.1
                  have p549_1 := h549c.2.1
                  have p549_2 := h549c.2.2.1
                  have p549_3 := h549c.2.2.2
                  linarith only [hlam, p549_0]
            · linarith only [h517, h521, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
            · rcases m.htr 2 4 5 (by decide) (by decide) with h577 | h577
              · rcases h5bigk with h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c | h578c
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h0, hlam, p578_1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h0, h519, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h0, h519, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h0, h519, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h519, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h519, h576, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h519, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h519, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h516, hlam, p578_1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p578_1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h516, hc35, hlam, hphi, ht0b, ht5b, p578_1, u0elo4]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h520, h576, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo3]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h517, hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h519, hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h576, hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p578_1, u3elo4]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h518, hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p578_1]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h577, hlam, p578_0]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [h516, h577, hc35, hlam, hphi, ht0b, ht5b, p578_1, u0elo4]
                · have p578_0 := h578c.1
                  have p578_1 := h578c.2.1
                  have p578_2 := h578c.2.2.1
                  have p578_3 := h578c.2.2.2
                  linarith only [hlam, p578_0]
              · linarith only [h518, h520, h576, h577, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h517, h576, hc23, hlam, hphi, u3elo0]
        · linarith only [h517, h519, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h607 | h607
        · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
          · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
            · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
              · linarith only [h516, h518, h610, hlam]
              · rcases h5bigk with h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c | h612c
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [hlam, p612_0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h0, hlam, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p612_1, u0elo4]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h517, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p612_1, u3elo0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h518, hlam, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [hlam, p612_0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h607, h608, h610, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p612_1, u3elo1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h607, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p612_1, u3elo1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h607, h608, h610, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p612_1, u3elo1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h516, hlam, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [hlam, p612_0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h516, hc35, hlam, hphi, ht0b, ht5b, p612_1, u0elo4]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h610, hlam, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h517, hlam, p612_0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h607, hlam, p612_0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h609, hlam, p612_0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [hlam, p612_0]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h518, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p612_1, u3elo4]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [h608, h610, hc34, hc45, hlam, hphi, p612_1]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  rcases p612_3 (m.d 0 5) (by simp) with h636 | h636
                  · linarith only [h518, h636, hlam]
                  · linarith only [h517, h636, hlam]
                · have p612_0 := h612c.1
                  have p612_1 := h612c.2.1
                  have p612_2 := h612c.2.2.1
                  have p612_3 := h612c.2.2.2
                  linarith only [hlam, p612_0]
            · linarith only [h517, h609, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h641 | h641
            · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
              · linarith only [h516, h518, h642, hlam]
              · linarith only [h608, h641, h642, hlam]
            · linarith only [h517, h641, hc23, hlam, hphi, u3elo0]
        · linarith only [h517, h607, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h647 | h647
      · rcases m.htr 1 3 5 (by decide) (by decide) with h648 | h648
        · linarith only [h517, h648, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
          · rcases m.htr 2 3 5 (by decide) (by decide) with h651 | h651
            · linarith only [h0, h648, h651, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h653 | h653
              · linarith only [h650, h651, h653, hlam]
              · rcases h5bigk with h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c | h655c
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [hlam, p655_0]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h0, hlam, p655_1]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h650, h651, hc34, hlam, hphi, ht0b, ht45, ht5b, p655_1, u0elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h517, hlam, p655_1]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h517, h650, h651, h653, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p655_1, u3elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p655_1]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [hlam, p655_0]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h648, h650, h651, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p655_1, u3elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h648, hlam, p655_1]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h648, h650, h651, h653, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p655_1, u3elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h516, hlam, p655_1]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h647, h653, hc15, hlam, hphi, ht0b, ht5b, p655_1, u0elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [hlam, p655_0]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h651, hlam, p655_1]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h653, hlam, p655_1]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p655_1, u3elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p655_1, u3elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p655_1, u3elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [hlam, p655_0]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h650, h651, h653, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p655_1, u3elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h647, hlam, p655_0]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h0, h647, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p655_1, u0elo4]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h647, h650, h651, hc34, hlam, hphi, ht0b, ht45, ht5b, p655_1, u0elo3]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [h0, h647, h648, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p655_1, u0elo3]
                · have p655_0 := h655c.1
                  have p655_1 := h655c.2.1
                  have p655_2 := h655c.2.2.1
                  have p655_3 := h655c.2.2.2
                  linarith only [hlam, p655_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h681 | h681
            · linarith only [h0, h648, h650, h681, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h683 | h683
              · rcases h5bigk with h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hlam, p684_0]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h0, hlam, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p684_1, u0elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h517, hlam, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h0, h648, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h648, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hlam, p684_0]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h648, h681, hc23, hlam, hphi, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h648, hlam, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h648, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h516, hlam, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hlam, p684_0]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h681, hlam, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h516, hc45, hlam, hphi, ht0b, ht5b, p684_1, u0elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hlam, p684_0]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p684_1, u3elo4]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h647, hlam, p684_0]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h683, hlam, p684_0]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [h648, h683, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p684_1]
                · have p684_0 := h684c.1
                  have p684_1 := h684c.2.1
                  have p684_2 := h684c.2.2.1
                  have p684_3 := h684c.2.2.2
                  linarith only [hlam, p684_0]
              · rcases h5bigk with h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c | h710c
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [hlam, p710_0]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h0, hlam, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [hc25, hlam, hphi, ht0b, ht5b, p710_1, u0elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h517, hlam, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h517, h650, h683, hc23, hlam, hphi, p710_1, u3elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [hlam, p710_0]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h648, h650, h683, hc23, hlam, hphi, p710_1, u3elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h648, hlam, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h648, h650, h683, hc23, hlam, hphi, p710_1, u3elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h516, hlam, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [hlam, p710_0]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h681, hlam, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h683, hlam, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h647, h650, h683, hc23, hlam, hphi, p710_1, u3elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h0, h647, h650, h683, hc23, hlam, hphi, p710_1, u3elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p710_1, u3elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [hlam, p710_0]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h650, h683, hc23, hlam, hphi, p710_1, u3elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h647, hlam, p710_0]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h0, h647, hlam, p710_1]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h647, h650, h683, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p710_1, u0elo4]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [h0, h647, h648, hc05, hlam, hphi, ht0b, ht5b, p710_1, u0elo3]
                · have p710_0 := h710c.1
                  have p710_1 := h710c.2.1
                  have p710_2 := h710c.2.2.1
                  have p710_3 := h710c.2.2.2
                  linarith only [hlam, p710_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h736 | h736
        · linarith only [h517, h736, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h738 | h738
          · rcases m.htr 2 3 5 (by decide) (by decide) with h739 | h739
            · linarith only [h0, h736, h739, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
              · linarith only [h647, h738, h739, h741, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases h5bigk with h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c | h743c
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [hlam, p743_0]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h0, hlam, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h739, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p743_1, u0elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h517, hlam, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h647, hlam, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [hlam, p743_0]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h736, h738, h739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p743_1, u3elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h736, hlam, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h516, h647, h736, h738, h739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p743_1, u3elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h516, hlam, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h516, hc15, hlam, hphi, ht0b, ht5b, p743_1, u0elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [hlam, p743_0]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h739, hlam, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h741, hlam, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p743_1, u3elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p743_1, u3elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p743_1, u3elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [hlam, p743_0]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h516, h647, h738, h739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p743_1, u3elo4]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h516, h738, h739, hc34, hc45, hlam, hphi, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h738, h739, hc34, hc45, hlam, hphi, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [h736, hc13, hc45, hlam, hphi, ht34, p743_1]
                · have p743_0 := h743c.1
                  have p743_1 := h743c.2.1
                  have p743_2 := h743c.2.2.1
                  have p743_3 := h743c.2.2.2
                  linarith only [hlam, p743_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h769 | h769
            · linarith only [h0, h736, h738, h769, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h771 | h771
              · linarith only [h516, h647, h771, hlam]
              · rcases h5bigk with h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c | h773c
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [hlam, p773_0]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h0, hlam, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h0, h736, h771, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h517, hlam, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h647, hlam, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h736, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [hlam, p773_0]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h736, h738, h771, hc23, hlam, hphi, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h736, hlam, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h736, h738, h771, hc23, hlam, hphi, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h516, hlam, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [hlam, p773_0]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h769, hlam, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h771, hlam, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [hlam, p773_0]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h738, h771, hc23, hlam, hphi, p773_1, u3elo4]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h738, h771, hc23, hc45, hlam, hphi, ht34, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [h517, hc03, hc45, hlam, hphi, ht34, p773_1]
                · have p773_0 := h773c.1
                  have p773_1 := h773c.2.1
                  have p773_2 := h773c.2.2.1
                  have p773_3 := h773c.2.2.2
                  linarith only [hlam, p773_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h799 | h799
    · rcases m.htr 0 4 5 (by decide) (by decide) with h800 | h800
      · rcases m.htr 1 3 5 (by decide) (by decide) with h801 | h801
        · rcases m.htr 2 3 4 (by decide) (by decide) with h802 | h802
          · rcases m.htr 2 3 5 (by decide) (by decide) with h803 | h803
            · rcases m.htr 2 4 5 (by decide) (by decide) with h804 | h804
              · rcases h5bigk with h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h0, hlam, p805_1]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h516, hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p805_1, u0elo4]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h799, hc45, hlam, hphi, ht0b, ht5b, p805_1, u0elo2]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h801, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo1]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h801, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo1]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h801, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo1]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h801, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo1]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p805_1]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h802, h804, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo2]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h802, h804, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo2]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h802, h804, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo2]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h799, hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h801, hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h803, hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p805_1, u3elo4]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h800, hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h0, h800, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p805_1, u0elo3]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h804, hlam, p805_0]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [h800, hc35, hlam, hphi, ht0b, ht5b, p805_1, u0elo4]
                · have p805_0 := h805c.1
                  have p805_1 := h805c.2.1
                  have p805_2 := h805c.2.2.1
                  have p805_3 := h805c.2.2.2
                  linarith only [hlam, p805_0]
              · linarith only [h516, h800, h804, hlam]
            · linarith only [h799, h803, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
            · linarith only [h516, h802, h833, hc02, hlam, hphi, ht23, u3elo3]
            · linarith only [h799, h833, hc23, hlam, hphi, u3elo0]
        · linarith only [h799, h801, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h837 | h837
        · rcases m.htr 2 3 4 (by decide) (by decide) with h838 | h838
          · rcases m.htr 2 3 5 (by decide) (by decide) with h839 | h839
            · rcases m.htr 2 4 5 (by decide) (by decide) with h840 | h840
              · rcases h5bigk with h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c | h841c
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h0, hlam, p841_1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h516, hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h800, h838, h840, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p841_1, u3elo2]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h800, hlam, p841_1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h0, h837, hc01, hlam, hphi, ht12, ht23, p841_1, u3elo1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h516, h837, hc02, hlam, hphi, ht23, p841_1, u3elo1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h837, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p841_1, u3elo1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h837, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p841_1, u3elo1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p841_1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h838, h840, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p841_1, u3elo2]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h838, h840, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p841_1, u3elo2]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h800, h838, h840, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p841_1, u3elo2]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h799, hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h837, hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h839, hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h800, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p841_1, u3elo4]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p841_1]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h0, h838, h840, hc01, hlam, hphi, ht12, ht23, p841_1, u3elo2]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h840, hlam, p841_0]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [h838, h840, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p841_1, u3elo2]
                · have p841_0 := h841c.1
                  have p841_1 := h841c.2.1
                  have p841_2 := h841c.2.2.1
                  have p841_3 := h841c.2.2.2
                  linarith only [hlam, p841_0]
              · rcases h5bigk with h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h0, hlam, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h516, hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p867_1, u0elo4]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h800, hlam, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h837, h840, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p867_1, u3elo1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h837, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p867_1, u3elo1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h516, h837, h840, hc02, hlam, hphi, ht23, p867_1, u3elo1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h839, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p867_1, u3elo2]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h839, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p867_1, u3elo2]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h840, hlam, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h799, hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h837, hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h839, hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [hlam, p867_0]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p867_1, u3elo4]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [h516, hc02, hc45, hlam, hphi, ht23, ht34, p867_1]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  rcases p867_3 (m.d 0 5) (by simp) with h891 | h891
                  · linarith only [h800, h891, hlam]
                  · linarith only [h799, h891, hlam]
                · have p867_0 := h867c.1
                  have p867_1 := h867c.2.1
                  have p867_2 := h867c.2.2.1
                  have p867_3 := h867c.2.2.2
                  linarith only [hlam, p867_0]
            · linarith only [h799, h839, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h896 | h896
            · linarith only [h516, h838, h896, hc02, hlam, hphi, ht23, u3elo3]
            · linarith only [h799, h896, hc23, hlam, hphi, u3elo0]
        · linarith only [h799, h837, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
      · rcases m.htr 1 3 5 (by decide) (by decide) with h901 | h901
        · linarith only [h799, h901, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h903 | h903
          · rcases m.htr 2 3 5 (by decide) (by decide) with h904 | h904
            · linarith only [h0, h901, h904, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h906 | h906
              · linarith only [h516, h903, h904, h906, hc02, hlam, hphi, ht23, u3elo4]
              · linarith only [h516, h900, h906, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h909 | h909
            · linarith only [h901, h903, h909, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h911 | h911
              · rcases h5bigk with h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hlam, p912_0]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h0, hlam, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h516, hlam, p912_0]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h799, hlam, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hc45, hlam, hphi, ht0b, ht5b, p912_1, u0elo4]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hlam, p912_0]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h516, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h901, hlam, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h901, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p912_1, u3elo4]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h903, h911, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p912_1, u3elo3]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hlam, p912_0]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h909, hlam, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h903, h911, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p912_1, u3elo3]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p912_1, u3elo4]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p912_1, u3elo4]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p912_1, u3elo4]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hlam, p912_0]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p912_1, u3elo4]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h900, hlam, p912_0]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p912_1]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h911, hlam, p912_0]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [h900, hc35, hlam, hphi, ht0b, ht5b, p912_1, u0elo4]
                · have p912_0 := h912c.1
                  have p912_1 := h912c.2.1
                  have p912_2 := h912c.2.2.1
                  have p912_3 := h912c.2.2.2
                  linarith only [hlam, p912_0]
              · linarith only [h516, h900, h911, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h939 | h939
        · linarith only [h799, h939, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h941 | h941
          · rcases m.htr 2 3 5 (by decide) (by decide) with h942 | h942
            · linarith only [h0, h939, h942, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h944 | h944
              · linarith only [h900, h941, h942, h944, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases h5bigk with h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [hlam, p946_0]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h0, hlam, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h516, hlam, p946_0]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h799, hlam, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h900, hlam, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [hlam, p946_0]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h516, h939, hc02, hlam, hphi, ht23, p946_1, u3elo4]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h939, hlam, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h516, h939, h944, hc02, hlam, hphi, ht23, p946_1, u3elo4]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h942, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p946_1, u3elo4]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [hlam, p946_0]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h942, hlam, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h944, hlam, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p946_1, u3elo4]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p946_1, u3elo4]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p946_1, u3elo4]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [hlam, p946_0]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p946_1, u3elo4]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h516, hc02, hc45, hlam, hphi, ht23, ht34, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [h939, hc13, hc45, hlam, hphi, ht34, p946_1]
                · have p946_0 := h946c.1
                  have p946_1 := h946c.2.1
                  have p946_2 := h946c.2.2.1
                  have p946_3 := h946c.2.2.2
                  linarith only [hlam, p946_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h972 | h972
            · linarith only [h0, h939, h941, h972, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h974 | h974
              · rcases h5bigk with h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [hlam, p975_0]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h0, hlam, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h516, hlam, p975_0]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h799, hlam, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h900, hlam, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [hlam, p975_0]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h516, h900, h941, h974, hc02, hc04, hc15, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p975_1, u3elo3]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h939, hlam, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h900, h939, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p975_1, u3elo4]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h941, h974, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p975_1, u3elo3]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [hlam, p975_0]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h972, hlam, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h900, h941, h974, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p975_1, u3elo3]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p975_1, u3elo4]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p975_1, u3elo4]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p975_1, u3elo4]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [hlam, p975_0]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h900, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p975_1, u3elo4]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p975_1]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h0, h941, h974, hc01, hlam, hphi, ht12, ht23, p975_1, u3elo3]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h974, hlam, p975_0]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [h941, h974, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p975_1, u3elo3]
                · have p975_0 := h975c.1
                  have p975_1 := h975c.2.1
                  have p975_2 := h975c.2.2.1
                  have p975_3 := h975c.2.2.2
                  linarith only [hlam, p975_0]
              · rcases h5bigk with h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [hlam, p1001_0]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h0, hlam, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h516, hlam, p1001_0]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h799, hlam, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h900, hlam, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h0, hc01, hc15, hlam, hphi, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [hlam, p1001_0]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h516, h939, hc02, hlam, hphi, ht23, p1001_1, u3elo4]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h939, hlam, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h516, h939, h974, hc02, hlam, hphi, ht23, p1001_1, u3elo4]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h972, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1001_1, u3elo4]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [hlam, p1001_0]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h972, hlam, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h974, hlam, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1001_1, u3elo4]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1001_1, u3elo4]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1001_1, u3elo4]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [hlam, p1001_0]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1001_1, u3elo4]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h516, hc02, hc45, hlam, hphi, ht23, ht34, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [h799, hc03, hc45, hlam, hphi, ht34, p1001_1]
                · have p1001_0 := h1001c.1
                  have p1001_1 := h1001c.2.1
                  have p1001_2 := h1001c.2.2.1
                  have p1001_3 := h1001c.2.2.2
                  linarith only [hlam, p1001_0]

theorem r1l7_10_12_13_25_L_0_L_I_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_0_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_0_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
