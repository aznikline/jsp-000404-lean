import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h5 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h519 | h519
  · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
    · rcases m.htr 1 2 5 (by decide) (by decide) with h521 | h521
      · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
        · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
          · rcases m.htr 2 3 5 (by decide) (by decide) with h524 | h524
            · linarith only [h0, h519, h524, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h526 | h526
              · linarith only [h2, h5, h526, hlam]
              · rcases h2bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, h521, h524, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, h523, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  rcases p528_3 (m.d 0 2) (by simp) with h532 | h532
                  · rcases p528_3 (m.d 1 2) (by simp) with h533 | h533
                    · linarith only [h0, h533, hlam]
                    · linarith only [h520, h533, hlam]
                  · linarith only [h532, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, h523, h524, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, hlam, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h523, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, h523, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, h523, h524, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h1, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h519, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h523, h524, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h524, hlam, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h2, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h520, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h523, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h526, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h3, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h521, hlam, p528_0]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [h0, h521, h523, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p528_1]
                · have p528_0 := h528c.1
                  have p528_1 := h528c.2.1
                  have p528_2 := h528c.2.2.1
                  have p528_3 := h528c.2.2.2
                  linarith only [hlam, p528_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h558 | h558
            · linarith only [h0, h1, h4, h523, h558, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h560 | h560
              · linarith only [h4, h5, h523, h560, hlam]
              · rcases h2bigk with h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h521, hc02, hlam, hphi, ht0b, ht5b, p562_1, u5ehi1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  rcases p562_3 (m.d 0 2) (by simp) with h565 | h565
                  · rcases p562_3 (m.d 1 2) (by simp) with h566 | h566
                    · linarith only [h0, h566, hlam]
                    · linarith only [h519, h566, hlam]
                  · linarith only [h565, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  rcases p562_3 (m.d 0 2) (by simp) with h570 | h570
                  · rcases p562_3 (m.d 1 2) (by simp) with h571 | h571
                    · linarith only [h0, h571, hlam]
                    · linarith only [h520, h571, hlam]
                  · linarith only [h570, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p562_1, u5ehi2]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, hlam, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, h523, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p562_1, u5ehi2]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h1, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h519, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h523, hlam, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h558, hlam, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h2, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h520, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h560, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h3, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h521, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, h521, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h596 | h596
          · linarith only [h519, h522, h596, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h598 | h598
            · linarith only [h4, h519, h522, h598, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h600 | h600
              · linarith only [h0, h2, h4, h5, h522, h600, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases h2bigk with h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c | h602c
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, h521, hc01, hlam, hphi, ht0b, ht5b, p602_1, u5ehi2]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  rcases p602_3 (m.d 0 2) (by simp) with h605 | h605
                  · rcases p602_3 (m.d 1 2) (by simp) with h606 | h606
                    · linarith only [h0, h606, hlam]
                    · linarith only [h519, h606, hlam]
                  · linarith only [h605, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  rcases p602_3 (m.d 0 2) (by simp) with h610 | h610
                  · rcases p602_3 (m.d 1 2) (by simp) with h611 | h611
                    · linarith only [h0, h611, hlam]
                    · linarith only [h520, h611, hlam]
                  · linarith only [h610, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p602_1, u5ehi2]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p602_1, u5ehi2]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h1, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h519, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h596, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h598, hlam, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h2, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h520, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h600, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h3, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h521, hlam, p602_0]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [h0, h521, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p602_1]
                · have p602_0 := h602c.1
                  have p602_1 := h602c.2.1
                  have p602_2 := h602c.2.2.1
                  have p602_3 := h602c.2.2.2
                  linarith only [hlam, p602_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h636 | h636
        · rcases m.htr 2 3 4 (by decide) (by decide) with h637 | h637
          · linarith only [h0, h3, h519, h521, h637, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h3, h519, h521, h636, h637, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
          · linarith only [h519, h636, h640, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h642 | h642
            · linarith only [h4, h519, h636, h642, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
              · linarith only [h0, h3, h5, h520, h521, h644, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h2bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, h520, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  rcases p646_3 (m.d 0 2) (by simp) with h649 | h649
                  · rcases p646_3 (m.d 1 2) (by simp) with h650 | h650
                    · linarith only [h0, h650, hlam]
                    · linarith only [h519, h650, hlam]
                  · linarith only [h649, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  rcases p646_3 (m.d 0 2) (by simp) with h654 | h654
                  · rcases p646_3 (m.d 1 2) (by simp) with h655 | h655
                    · linarith only [h0, h655, hlam]
                    · linarith only [h520, h655, hlam]
                  · linarith only [h654, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p646_1, u5ehi2]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, hlam, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, h640, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h521, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h1, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h519, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h640, hlam, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h642, hlam, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h2, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h520, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h644, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h3, hlam, p646_0]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [h0, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p646_1]
                · have p646_0 := h646c.1
                  have p646_1 := h646c.2.1
                  have p646_2 := h646c.2.2.1
                  have p646_3 := h646c.2.2.2
                  linarith only [hlam, p646_0]
    · linarith only [h2, h5, h519, h520, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h681 | h681
    · rcases m.htr 1 2 5 (by decide) (by decide) with h682 | h682
      · linarith only [h0, h1, h519, h682, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h684 | h684
        · rcases m.htr 2 3 4 (by decide) (by decide) with h685 | h685
          · rcases m.htr 2 3 5 (by decide) (by decide) with h686 | h686
            · rcases m.htr 2 4 5 (by decide) (by decide) with h687 | h687
              · linarith only [h2, h5, h687, hlam]
              · rcases h2bigk with h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, h681, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, h686, hc01, hlam, hphi, ht0b, ht5b, p689_1, u5ehi2]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  rcases p689_3 (m.d 0 2) (by simp) with h693 | h693
                  · rcases p689_3 (m.d 1 2) (by simp) with h694 | h694
                    · linarith only [h0, h694, hlam]
                    · linarith only [h681, h694, hlam]
                  · linarith only [h693, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, h681, h682, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, hlam, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h519, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h1, h682, h685, h686, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h682, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h1, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, h1, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, h1, hc01, hlam, hphi, ht0b, ht5b, p689_1, u5ehi2]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h2, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h681, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h685, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h687, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h3, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h3, h681, h685, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h686, hlam, p689_0]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [h0, h1, h685, h686, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p689_1]
                · have p689_0 := h689c.1
                  have p689_1 := h689c.2.1
                  have p689_2 := h689c.2.2.1
                  have p689_3 := h689c.2.2.2
                  linarith only [hlam, p689_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h719 | h719
              · linarith only [h5, h519, h681, h686, h719, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
              · rcases h2bigk with h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h0, h681, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h0, h519, h681, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  rcases p721_3 (m.d 0 2) (by simp) with h725 | h725
                  · rcases p721_3 (m.d 1 2) (by simp) with h726 | h726
                    · linarith only [h0, h726, hlam]
                    · linarith only [h681, h726, hlam]
                  · linarith only [h725, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h0, h519, h681, h685, h686, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h0, hlam, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h519, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h519, h685, h686, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h682, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h1, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h686, hc12, hc35, hlam, hphi, ht23, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h685, h686, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h686, hlam, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h2, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h681, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h685, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h719, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h3, hlam, p721_0]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h3, h681, h685, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h0, h3, h519, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [h0, h3, h685, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p721_1]
                · have p721_0 := h721c.1
                  have p721_1 := h721c.2.1
                  have p721_2 := h721c.2.2.1
                  have p721_3 := h721c.2.2.2
                  linarith only [hlam, p721_0]
          · linarith only [h0, h1, h4, h519, h681, h685, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h4, h5, h519, h681, h684, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
      · linarith only [h2, h5, h681, h753, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h755 | h755
        · rcases m.htr 2 3 4 (by decide) (by decide) with h756 | h756
          · rcases m.htr 2 3 5 (by decide) (by decide) with h757 | h757
            · rcases m.htr 2 4 5 (by decide) (by decide) with h758 | h758
              · linarith only [h2, h5, h758, hlam]
              · rcases h2bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  rcases p760_3 (m.d 0 2) (by simp) with h762 | h762
                  · rcases p760_3 (m.d 1 2) (by simp) with h763 | h763
                    · linarith only [h0, h763, hlam]
                    · rcases p760_3 (m.d 2 3) (by simp) with h765 | h765
                      · linarith only [h1, h765, hlam]
                      · linarith only [h519, h765, hlam]
                  · linarith only [h0, h762, hlam]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h0, h757, hc01, hlam, hphi, ht0b, ht5b, p760_1, u5ehi2]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h0, h681, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p760_1, u5ehi2]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h0, hlam, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h519, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h681, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h753, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h1, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h0, h1, h681, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h0, h1, h753, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h2, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h756, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h758, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h3, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h757, hlam, p760_0]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [h0, h1, h757, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                · have p760_0 := h760c.1
                  have p760_1 := h760c.2.1
                  have p760_2 := h760c.2.2.1
                  have p760_3 := h760c.2.2.2
                  linarith only [hlam, p760_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h792 | h792
              · linarith only [h2, h5, h792, hlam]
              · rcases h2bigk with h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c | h794c
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  rcases p794_3 (m.d 0 2) (by simp) with h796 | h796
                  · rcases p794_3 (m.d 1 2) (by simp) with h797 | h797
                    · linarith only [h0, h797, hlam]
                    · rcases p794_3 (m.d 2 3) (by simp) with h799 | h799
                      · linarith only [h1, h799, hlam]
                      · linarith only [h519, h799, hlam]
                  · linarith only [h0, h796, hlam]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, h681, h756, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, h681, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, h681, h756, h757, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, hlam, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h519, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h681, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h753, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h1, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, h1, h681, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h757, hlam, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h2, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h756, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h792, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h3, hlam, p794_0]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [h0, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p794_1]
                · have p794_0 := h794c.1
                  have p794_1 := h794c.2.1
                  have p794_2 := h794c.2.2.1
                  have p794_3 := h794c.2.2.2
                  linarith only [hlam, p794_0]
          · linarith only [h4, h5, h519, h756, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h827 | h827
          · rcases m.htr 2 3 5 (by decide) (by decide) with h828 | h828
            · rcases m.htr 2 4 5 (by decide) (by decide) with h829 | h829
              · linarith only [h2, h5, h829, hlam]
              · rcases h2bigk with h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  rcases p831_3 (m.d 0 2) (by simp) with h833 | h833
                  · rcases p831_3 (m.d 1 2) (by simp) with h834 | h834
                    · linarith only [h0, h834, hlam]
                    · rcases p831_3 (m.d 2 3) (by simp) with h836 | h836
                      · linarith only [h1, h836, hlam]
                      · linarith only [h519, h836, hlam]
                  · linarith only [h0, h833, hlam]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h0, h753, h828, hc01, hlam, hphi, ht0b, ht5b, p831_1, u5ehi1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h0, h519, h755, h827, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h0, h753, hc01, hlam, hphi, ht0b, ht5b, p831_1, u5ehi1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h0, hlam, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h519, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h681, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h753, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h1, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h0, h1, h519, h755, h827, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h0, h1, h753, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h2, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hc12, hc24, hlam, hphi, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h827, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h829, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h3, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hc12, hc25, hlam, hphi, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h828, hlam, p831_0]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [h0, h1, h828, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p831_1]
                · have p831_0 := h831c.1
                  have p831_1 := h831c.2.1
                  have p831_2 := h831c.2.2.1
                  have p831_3 := h831c.2.2.2
                  linarith only [hlam, p831_0]
            · linarith only [h519, h755, h827, h828, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h4, h5, h519, h827, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x0_x0 m hb2 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x0_x1 m hb2 hb5 h0 h1 h2 h3 h4 h5

end R2N4
