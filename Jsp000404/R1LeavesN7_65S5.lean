import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_65S4

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_23_L_0_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h449 | h449
  · rcases m.htr 0 3 5 (by decide) (by decide) with h450 | h450
    · rcases m.htr 1 2 3 (by decide) (by decide) with h451 | h451
      · linarith only [h0, h1, h451, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h453 | h453
        · rcases m.htr 2 3 4 (by decide) (by decide) with h454 | h454
          · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
            · rcases m.htr 3 4 5 (by decide) (by decide) with h456 | h456
              · rcases h3bigk with h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h1, h453, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p457_1]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h1, hlam, p457_1]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h0, h456, hc45, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h0, hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h451, hlam, p457_1]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h456, hc45, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo2]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h0, h456, hc45, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h1, hc02, hc23, hlam, hphi, p457_1]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h451, hc12, hc23, hlam, hphi, p457_1]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h456, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p457_1]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  rcases p457_3 (m.d 0 3) (by simp) with h472 | h472
                  · linarith only [h1, h472, hlam]
                  · linarith only [h450, h472, hlam]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h449, hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h449, h453, h456, hc03, hc45, hlam, hphi, ht0b, ht5b, p457_1]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h454, hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h0, h449, h456, hc45, hlam, hphi, ht01, ht0b, ht5b, p457_1, u1elo0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h450, hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h453, hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h455, hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [h456, hlam, p457_0]
                · have p457_0 := h457c.1
                  have p457_1 := h457c.2.1
                  have p457_2 := h457c.2.2.1
                  have p457_3 := h457c.2.2.2
                  linarith only [hlam, p457_0]
              · rcases h3bigk with h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, h453, h456, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u1elo0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h1, hlam, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u1elo0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, h456, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u1elo0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h451, hlam, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u1elo2]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h456, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p485_1, u1elo2]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h1, hc02, hc23, hlam, hphi, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h451, hc12, hc23, hlam, hphi, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  rcases p485_3 (m.d 0 3) (by simp) with h499 | h499
                  · linarith only [h1, h499, hlam]
                  · linarith only [h449, h499, hlam]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  rcases p485_3 (m.d 0 3) (by simp) with h502 | h502
                  · linarith only [h1, h502, hlam]
                  · linarith only [h450, h502, hlam]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h449, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h453, h456, hlam, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h454, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h456, hlam, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h450, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h453, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h455, hlam, p485_0]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [h0, h453, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p485_1]
                · have p485_0 := h485c.1
                  have p485_1 := h485c.2.1
                  have p485_2 := h485c.2.2.1
                  have p485_3 := h485c.2.2.2
                  linarith only [hlam, p485_0]
            · linarith only [h0, h453, h455, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h1, h449, h454, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h517 | h517
          · rcases m.htr 2 3 5 (by decide) (by decide) with h518 | h518
            · rcases m.htr 3 4 5 (by decide) (by decide) with h519 | h519
              · rcases h3bigk with h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h1, h451, hc12, hc23, hlam, hphi, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h1, hlam, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h1, h519, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p520_1, u1elo0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h0, hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h451, hlam, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h453, h519, hlam, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h453, hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h449, h451, h453, h519, hc12, hc23, hlam, hphi, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h451, hc12, hc23, hlam, hphi, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h451, h453, h519, hc12, hc23, hlam, hphi, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h451, h453, hc12, hc23, hlam, hphi, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h449, hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h0, h449, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p520_1, u1elo0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h517, hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h0, h449, hc35, hlam, hphi, ht01, ht0b, ht5b, p520_1, u1elo0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h450, hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h451, hc12, hc35, hlam, hphi, ht23, p520_1]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h518, hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [h519, hlam, p520_0]
                · have p520_0 := h520c.1
                  have p520_1 := h520c.2.1
                  have p520_2 := h520c.2.2.1
                  have p520_3 := h520c.2.2.2
                  linarith only [hlam, p520_0]
              · rcases h3bigk with h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h0, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p546_1, u1elo0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h1, hlam, p546_1]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h0, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p546_1, u1elo0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p546_1, u1elo0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h0, hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h451, hlam, p546_1]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p546_1, u1elo2]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h453, hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h1, hc02, hc23, hlam, hphi, p546_1]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h451, hc12, hc23, hlam, hphi, p546_1]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  rcases p546_3 (m.d 0 3) (by simp) with h560 | h560
                  · linarith only [h1, h560, hlam]
                  · linarith only [h449, h560, hlam]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h451, h453, hc12, hc23, hlam, hphi, p546_1]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h449, hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h451, h517, hc12, hc24, hlam, hphi, p546_1]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h517, hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h519, hlam, p546_1]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h450, hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h0, h450, h451, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p546_1, u1elo0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h518, hlam, p546_0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [h0, h450, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p546_1, u1elo0]
                · have p546_0 := h546c.1
                  have p546_1 := h546c.2.1
                  have p546_2 := h546c.2.2.1
                  have p546_3 := h546c.2.2.2
                  linarith only [hlam, p546_0]
            · linarith only [h0, h1, h450, h518, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · linarith only [h1, h449, h517, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h576 | h576
      · linarith only [h0, h1, h576, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h578 | h578
        · linarith only [h0, h450, h578, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
          · rcases m.htr 2 3 5 (by decide) (by decide) with h581 | h581
            · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
              · linarith only [h449, h450, h581, h582, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases h3bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h450, h576, h581, hc12, hc23, hlam, hphi, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h1, hlam, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h450, h581, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h450, hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h0, hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h576, hlam, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p584_1, u1elo2]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h578, hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h1, hc02, hc23, hlam, hphi, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h576, hc12, hc23, hlam, hphi, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  rcases p584_3 (m.d 0 3) (by simp) with h598 | h598
                  · linarith only [h1, h598, hlam]
                  · linarith only [h449, h598, hlam]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h449, h450, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h449, hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h449, h576, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h580, hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h582, hlam, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h449, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h576, h582, hc12, hc45, hlam, hphi, ht23, ht34, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h581, hlam, p584_0]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [h581, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p584_1]
                · have p584_0 := h584c.1
                  have p584_1 := h584c.2.1
                  have p584_2 := h584c.2.2.1
                  have p584_3 := h584c.2.2.2
                  linarith only [hlam, p584_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h612 | h612
              · linarith only [h0, h1, h449, h581, h612, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases h3bigk with h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h1, h576, hc12, hc23, hlam, hphi, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h1, hlam, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h1, h581, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h450, hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h0, hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h576, hlam, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p614_1, u1elo2]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h578, hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h581, h612, hc03, hc45, hlam, hphi, ht34, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h581, h612, hc13, hc45, hlam, hphi, ht34, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h581, h612, hc34, hc45, hlam, hphi, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h581, hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h449, hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h449, h576, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h580, hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [hlam, p614_0]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h612, hlam, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h612, hc03, hc45, hlam, hphi, ht34, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h576, h612, hc12, hc45, hlam, hphi, ht23, ht34, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h612, hc23, hc45, hlam, hphi, ht34, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [h612, hc34, hc45, hlam, hphi, p614_1]
                · have p614_0 := h614c.1
                  have p614_1 := h614c.2.1
                  have p614_2 := h614c.2.2.1
                  have p614_3 := h614c.2.2.2
                  linarith only [hlam, p614_0]
          · linarith only [h0, h1, h449, h580, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h641 | h641
    · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
      · linarith only [h0, h1, h642, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h644 | h644
        · rcases m.htr 2 3 4 (by decide) (by decide) with h645 | h645
          · rcases m.htr 2 3 5 (by decide) (by decide) with h646 | h646
            · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
              · rcases h3bigk with h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c | h648c
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h449, h642, h645, hc12, hc23, hlam, hphi, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h1, hlam, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h449, hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h449, h645, h647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h0, hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h642, hlam, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h449, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p648_1, u1elo2]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h647, hc45, hlam, hphi, ht01, ht0b, ht5b, p648_1, u1elo2]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h641, h647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h642, hc12, hc23, hlam, hphi, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h0, h449, h644, h647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  rcases p648_3 (m.d 0 3) (by simp) with h663 | h663
                  · linarith only [h1, h663, hlam]
                  · linarith only [h641, h663, hlam]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h0, h644, h645, h647, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h644, h645, h647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h645, hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h645, h647, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p648_1]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h641, hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h644, hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h646, hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [h647, hlam, p648_0]
                · have p648_0 := h648c.1
                  have p648_1 := h648c.2.1
                  have p648_2 := h648c.2.2.1
                  have p648_3 := h648c.2.2.2
                  linarith only [hlam, p648_0]
              · linarith only [h0, h449, h644, h647, hlam]
            · linarith only [h0, h449, h644, h646, hc23, hc34, hlam, hphi]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
            · rcases m.htr 3 4 5 (by decide) (by decide) with h679 | h679
              · rcases h3bigk with h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h1, h645, hc13, hc34, hlam, hphi, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h1, hlam, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h449, hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h1, h645, h679, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h0, hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h642, hlam, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h1, h645, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p680_1, u1elo2]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p680_1, u1elo2]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h0, h645, hc13, hc34, hlam, hphi, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h645, hc13, hc34, hlam, hphi, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h645, hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h645, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h0, h644, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h644, h679, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p680_1]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  rcases p680_3 (m.d 0 3) (by simp) with h700 | h700
                  · linarith only [h449, h700, hlam]
                  · linarith only [h641, h700, hlam]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h641, hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h644, hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h678, hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [h679, hlam, p680_0]
                · have p680_0 := h680c.1
                  have p680_1 := h680c.2.1
                  have p680_2 := h680c.2.2.1
                  have p680_3 := h680c.2.2.2
                  linarith only [hlam, p680_0]
              · linarith only [h1, h645, h679, hc02, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h1, h644, h678, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
        · linarith only [h449, h641, h644, hc13, hc34, hlam, hphi]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h711 | h711
      · linarith only [h0, h1, h711, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h713 | h713
        · linarith only [h0, h641, h713, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h715 | h715
          · rcases m.htr 2 3 5 (by decide) (by decide) with h716 | h716
            · rcases m.htr 3 4 5 (by decide) (by decide) with h717 | h717
              · rcases h3bigk with h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c | h718c
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h641, h711, h715, h717, hc12, hc23, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h1, hlam, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h449, hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h641, hlam, p718_0]
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
                  linarith only [h711, hlam, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h641, h717, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p718_1, u1elo2]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h713, hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h1, hc02, hc23, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h711, hc12, hc23, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h0, h641, h711, h717, hc12, hc23, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h0, h641, h711, hc12, hc23, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h0, h711, h715, hc12, hc24, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h711, h715, hc12, hc23, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h715, hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h0, h641, h711, h715, hc12, hc23, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h0, h711, h716, hc12, hc25, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h711, h716, hc12, hc25, hlam, hphi, p718_1]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h716, hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [h717, hlam, p718_0]
                · have p718_0 := h718c.1
                  have p718_1 := h718c.2.1
                  have p718_2 := h718c.2.2.1
                  have p718_3 := h718c.2.2.2
                  linarith only [hlam, p718_0]
              · rcases h3bigk with h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c | h744c
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p744_1, u1elo0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h1, hlam, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h449, hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h641, hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h0, hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h711, hlam, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h449, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p744_1, u1elo2]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h713, hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h1, hc02, hc23, hlam, hphi, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h711, hc12, hc23, hlam, hphi, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h0, h449, h711, hc12, hc23, hlam, hphi, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h0, h641, h711, hc12, hc23, hlam, hphi, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h0, h711, hc12, hc34, hlam, hphi, ht23, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h711, hc12, hc34, hlam, hphi, ht23, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h715, hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h717, hlam, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h0, h711, hc12, hc35, hlam, hphi, ht23, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h711, hc12, hc35, hlam, hphi, ht23, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h716, hlam, p744_0]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [h0, h449, h711, hc12, hc35, hlam, hphi, ht23, p744_1]
                · have p744_0 := h744c.1
                  have p744_1 := h744c.2.1
                  have p744_2 := h744c.2.2.1
                  have p744_3 := h744c.2.2.2
                  linarith only [hlam, p744_0]
            · linarith only [h0, h449, h711, h715, h716, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
            · linarith only [h0, h641, h711, h715, h771, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h773 | h773
              · rcases h3bigk with h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c | h774c
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h0, h711, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p774_1, u1elo0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h1, hlam, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h449, hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h641, hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h0, hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h711, hlam, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h1, h771, h773, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p774_1, u1elo2]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h713, hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h771, h773, hc03, hc34, hlam, hphi, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h771, h773, hc13, hc34, hlam, hphi, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h715, hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h771, hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h1, hc02, hc34, hlam, hphi, ht23, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h711, hc12, hc34, hlam, hphi, ht23, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h0, h641, h711, hc12, hc34, hlam, hphi, ht23, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h0, h711, hc12, hc35, hlam, hphi, ht23, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h711, hc12, hc35, hlam, hphi, ht23, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h1, hc02, hc35, hlam, hphi, ht23, p774_1]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [h773, hlam, p774_0]
                · have p774_0 := h774c.1
                  have p774_1 := h774c.2.1
                  have p774_2 := h774c.2.2.1
                  have p774_3 := h774c.2.2.2
                  linarith only [hlam, p774_0]
              · linarith only [h1, h715, h773, hc02, hc45, hlam, hphi, ht23, ht34]

theorem r1l7_11_23_L_0_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_23_L_0_H_I_x0_x0 m hb1 hb3 h0 h1
  · exact r1l7_11_23_L_0_H_I_x0_x1 m hb1 hb3 h0 h1

end R2N4
