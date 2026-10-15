import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h569 | h569
  · rcases m.htr 0 2 4 (by decide) (by decide) with h570 | h570
    · rcases m.htr 0 2 5 (by decide) (by decide) with h571 | h571
      · linarith only [h0, h2, h571, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h573 | h573
        · rcases m.htr 0 3 5 (by decide) (by decide) with h574 | h574
          · linarith only [h1, h2, h574, hlam]
          · linarith only [h573, h574, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h577 | h577
          · linarith only [h573, h577, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h579 | h579
            · linarith only [h0, h2, h570, h579, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h581 | h581
              · linarith only [h0, h2, h569, h577, h581, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h569, h571, h581, hc35, hlam, hphi, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h584 | h584
      · linarith only [h0, h2, h584, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h586 | h586
        · linarith only [h569, h570, h586, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h588 | h588
          · linarith only [h586, h588, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h590 | h590
            · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
              · linarith only [h569, h570, h588, h591, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · linarith only [h569, h584, h591, hc35, hlam, hphi, u3ehi2]
            · linarith only [h569, h570, h590, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h595 | h595
    · rcases m.htr 0 2 5 (by decide) (by decide) with h596 | h596
      · linarith only [h1, h2, h569, h596, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h598 | h598
        · rcases m.htr 0 3 5 (by decide) (by decide) with h599 | h599
          · linarith only [h1, h2, h599, hlam]
          · linarith only [h598, h599, hc35, hlam, hphi, u3ehi3]
        · linarith only [h569, h595, h598, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h603 | h603
      · linarith only [h0, h2, h603, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h605 | h605
        · rcases m.htr 0 3 5 (by decide) (by decide) with h606 | h606
          · linarith only [h1, h2, h606, hlam]
          · linarith only [h605, h606, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h609 | h609
          · linarith only [h605, h609, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h611 | h611
            · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
              · rcases h0bigk with h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c | h613c
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [hlam, p613_0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h0, h1, h2, h609, h612, hc12, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p613_1, u3ehi1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1, u3ehi1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h2, h609, h612, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h2, hlam, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h0, hlam, p613_0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [hlam, p613_0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h569, hlam, p613_0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h595, hlam, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h603, hlam, p613_0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h1, hlam, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h0, h1, h2, h609, h612, hc12, hc23, hlam, hphi, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [hlam, p613_0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h605, hlam, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h609, hlam, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p613_1, u3ehi1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h0, h595, hc12, hc24, hlam, hphi, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h605, hc34, hlam, hphi, p613_1, u3ehi0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [hlam, p613_0]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h1, h2, h605, hc34, hlam, hphi, p613_1, u3ehi1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h1, h609, h612, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p613_1, u3ehi1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h0, h609, h612, hc12, hc23, hlam, hphi, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h1, h609, h612, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p613_1, u3ehi1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [h611, hlam, p613_1]
                · have p613_0 := h613c.1
                  have p613_1 := h613c.2.1
                  have p613_2 := h613c.2.2.1
                  have p613_3 := h613c.2.2.2
                  linarith only [hlam, p613_0]
              · rcases h0bigk with h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [hlam, p639_0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h0, h2, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h1, h2, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p639_1, u3ehi1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h2, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h2, hlam, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h0, hlam, p639_0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [hlam, p639_0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h569, hlam, p639_0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h595, hlam, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h603, hlam, p639_0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h1, hlam, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h0, h1, h2, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [hlam, p639_0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h605, hlam, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h609, hlam, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h0, h595, hc12, hc24, hlam, hphi, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h605, hc34, hlam, hphi, p639_1, u3ehi0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [hlam, p639_0]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h1, h2, h605, hc34, hlam, hphi, p639_1, u3ehi1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p639_1, u3ehi1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h0, h603, h612, hc12, hc35, hlam, hphi, ht23, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h1, h603, h612, hc35, hlam, hphi, p639_1, u3ehi1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [h611, hlam, p639_1]
                · have p639_0 := h639c.1
                  have p639_1 := h639c.2.1
                  have p639_2 := h639c.2.2.1
                  have p639_3 := h639c.2.2.2
                  linarith only [hlam, p639_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h665 | h665
              · rcases h0bigk with h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c | h666c
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h0, h2, h609, h665, hc12, hc23, hlam, hphi, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h1, h2, h609, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p666_1, u3ehi1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h2, h609, h665, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h2, hlam, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h0, hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h569, hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h595, hlam, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h603, hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h1, hlam, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h0, h1, h2, h609, h665, hc12, hc23, hlam, hphi, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h605, hlam, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h609, hlam, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h0, h595, hc12, hc24, hlam, hphi, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h1, h605, hc34, hlam, hphi, p666_1, u3ehi1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h611, hlam, p666_0]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h1, h609, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p666_1, u3ehi1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h0, h609, h665, hc12, hc23, hlam, hphi, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h1, h609, h665, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p666_1, u3ehi1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [h609, h665, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p666_1]
                · have p666_0 := h666c.1
                  have p666_1 := h666c.2.1
                  have p666_2 := h666c.2.2.1
                  have p666_3 := h666c.2.2.2
                  linarith only [hlam, p666_0]
              · rcases h0bigk with h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c | h692c
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, h2, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h1, h2, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p692_1, u3ehi1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h1, h605, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1, u3ehi1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h2, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h569, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h595, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h603, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h1, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, h1, h2, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h605, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h609, hlam, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h611, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, h611, hc12, hc45, hlam, hphi, ht23, ht34, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h611, hc45, hlam, hphi, ht34, p692_1, u3ehi0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h611, hlam, p692_0]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h1, h603, h665, hc35, hlam, hphi, p692_1, u3ehi1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, h603, h665, hc12, hc35, hlam, hphi, ht23, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h1, h603, h665, hc35, hlam, hphi, p692_1, u3ehi1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [h0, h595, h603, h665, hc12, hc35, hlam, hphi, ht23, p692_1]
                · have p692_0 := h692c.1
                  have p692_1 := h692c.2.1
                  have p692_2 := h692c.2.2.1
                  have p692_3 := h692c.2.2.2
                  linarith only [hlam, p692_0]

set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h718 | h718
  · rcases m.htr 0 2 3 (by decide) (by decide) with h719 | h719
    · linarith only [h0, h1, h719, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h721 | h721
      · rcases m.htr 0 2 5 (by decide) (by decide) with h722 | h722
        · rcases m.htr 0 3 4 (by decide) (by decide) with h723 | h723
          · rcases m.htr 0 3 5 (by decide) (by decide) with h724 | h724
            · rcases m.htr 0 4 5 (by decide) (by decide) with h725 | h725
              · rcases m.htr 2 3 5 (by decide) (by decide) with h726 | h726
                · rcases h0bigk with h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h721, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, h722, h725, h726, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, h722, h726, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h719, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h722, h725, h726, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, h1, h722, h726, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h719, hc01, hc23, hlam, hphi, ht12, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h719, hc02, hc23, hlam, hphi, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h719, h722, h725, h726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h719, h722, h726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, h722, h726, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h721, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h723, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h0, h721, h722, h726, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h718, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h722, hlam, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h724, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h725, hlam, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                · linarith only [h719, h723, h726, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h754 | h754
                · rcases h0bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h722, h754, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p755_1, u3ehi4]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, h723, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, h723, h725, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h0, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h719, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h719, h723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h719, h723, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h719, hc01, hc23, hlam, hphi, ht12, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h719, hc02, hc23, hlam, hphi, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h719, h723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h719, h723, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h0, h722, h754, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p755_1, u3ehi4]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h721, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h723, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h725, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h718, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h722, hlam, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h724, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h1, h718, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                · linarith only [h719, h721, h723, h754, hc35, hlam, hphi, u3ehi3]
            · linarith only [h723, h724, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1, h721, h723, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h784 | h784
          · rcases m.htr 0 3 5 (by decide) (by decide) with h785 | h785
            · rcases m.htr 0 4 5 (by decide) (by decide) with h786 | h786
              · linarith only [h721, h722, h786, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h788 | h788
                · rcases h0bigk with h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h784, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p789_1, u3ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, h721, h722, h784, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p789_1, u3ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h0, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h719, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h784, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p789_1, u3ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h722, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, hc01, hc13, hlam, hphi, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h719, hc02, hc23, hlam, hphi, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h719, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p789_1, u3ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h719, h721, h722, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p789_1, u3ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h786, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h721, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h784, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h786, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h718, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, h718, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p789_1]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h785, hlam, p789_0]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [h1, h718, h784, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p789_1, u3ehi3]
                  · have p789_0 := h789c.1
                    have p789_1 := h789c.2.1
                    have p789_2 := h789c.2.2.1
                    have p789_3 := h789c.2.2.2
                    linarith only [hlam, p789_0]
                · linarith only [h719, h785, h788, hlam]
            · linarith only [h784, h785, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1, h721, h784, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h818 | h818
        · rcases m.htr 0 3 4 (by decide) (by decide) with h819 | h819
          · rcases m.htr 0 3 5 (by decide) (by decide) with h820 | h820
            · rcases m.htr 0 4 5 (by decide) (by decide) with h821 | h821
              · rcases m.htr 2 3 5 (by decide) (by decide) with h822 | h822
                · rcases h0bigk with h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h818, h822, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p823_1, u3ehi4]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h1, hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h0, hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h719, hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h721, hlam, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h721, h821, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h719, hc01, hc23, hlam, hphi, ht12, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h719, hc02, hc23, hlam, hphi, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h719, h721, h818, h822, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p823_1, u3ehi4]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h719, h818, h822, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p823_1, u3ehi4]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h0, h818, h822, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p823_1, u3ehi4]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h721, h818, h822, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p823_1, u3ehi4]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h819, hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h719, h818, h819, h822, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p823_1, u3ehi4]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h718, hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h818, hlam, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h820, hlam, p823_0]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [h821, hlam, p823_1]
                  · have p823_0 := h823c.1
                    have p823_1 := h823c.2.1
                    have p823_2 := h823c.2.2.1
                    have p823_3 := h823c.2.2.2
                    linarith only [hlam, p823_0]
                · linarith only [h719, h819, h822, hc35, hlam, hphi, u3ehi3]
              · linarith only [h721, h818, h821, hlam]
            · linarith only [h819, h820, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h852 | h852
            · linarith only [h819, h852, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1, h718, h852, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h855 | h855
          · rcases m.htr 0 3 5 (by decide) (by decide) with h856 | h856
            · rcases m.htr 0 4 5 (by decide) (by decide) with h857 | h857
              · rcases m.htr 2 3 5 (by decide) (by decide) with h858 | h858
                · rcases h0bigk with h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c | h859c
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h1, h719, hc02, hc23, hlam, hphi, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h1, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h1, h856, h857, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h1, h856, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h0, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h719, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h721, hlam, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h818, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h719, hc01, hc23, hlam, hphi, ht12, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h0, h719, hc12, hc23, hlam, hphi, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h719, h856, h857, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h719, h856, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h0, h721, hc12, hc24, hlam, hphi, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h855, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h719, h855, h856, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p859_1, u3ehi4]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h718, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h0, h1, h718, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h856, hlam, p859_0]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [h857, hlam, p859_1]
                  · have p859_0 := h859c.1
                    have p859_1 := h859c.2.1
                    have p859_2 := h859c.2.2.1
                    have p859_3 := h859c.2.2.2
                    linarith only [hlam, p859_0]
                · linarith only [h719, h855, h858, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h886 | h886
                · rcases h0bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h1, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h719, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h721, hlam, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h818, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h719, hc01, hc23, hlam, hphi, ht12, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, h719, hc12, hc23, hlam, hphi, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, h719, h721, hc12, hc23, hlam, hphi, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, h719, h818, hc12, hc23, hlam, hphi, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, h1, h718, h857, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h855, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h857, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h718, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h0, h1, h718, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h856, hlam, p887_0]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [h1, h718, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p887_1]
                  · have p887_0 := h887c.1
                    have p887_1 := h887c.2.1
                    have p887_2 := h887c.2.2.1
                    have p887_3 := h887c.2.2.2
                    linarith only [hlam, p887_0]
                · linarith only [h719, h855, h886, hc35, hlam, hphi, u3ehi3]
            · linarith only [h855, h856, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h915 | h915
            · linarith only [h855, h915, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1, h718, h915, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h918 | h918
    · linarith only [h0, h1, h918, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h920 | h920
      · rcases m.htr 0 2 5 (by decide) (by decide) with h921 | h921
        · linarith only [h0, h718, h921, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h923 | h923
          · rcases m.htr 0 3 5 (by decide) (by decide) with h924 | h924
            · rcases m.htr 0 4 5 (by decide) (by decide) with h925 | h925
              · linarith only [h0, h718, h920, h925, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h927 | h927
                · rcases h0bigk with h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h718, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h1, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h718, h923, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p928_1, u3ehi3]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h718, hlam, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h0, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h918, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h923, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi3]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h921, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h918, hc01, hc23, hlam, hphi, ht12, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h918, hc02, hc23, hlam, hphi, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h918, h923, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p928_1, u3ehi3]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h0, h718, h918, hc12, hc23, hlam, hphi, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h0, h920, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h920, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h923, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h925, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h921, hc02, hc25, hlam, hphi, p928_1]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h924, hlam, p928_0]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [h923, h925, hc45, hlam, hphi, ht34, p928_1, u3ehi3]
                  · have p928_0 := h928c.1
                    have p928_1 := h928c.2.1
                    have p928_2 := h928c.2.2.1
                    have p928_3 := h928c.2.2.2
                    linarith only [hlam, p928_0]
                · linarith only [h918, h924, h927, hlam]
            · linarith only [h923, h924, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1, h920, h923, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h957 | h957
        · linarith only [h0, h718, h957, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h959 | h959
          · rcases m.htr 0 3 5 (by decide) (by decide) with h960 | h960
            · rcases m.htr 0 4 5 (by decide) (by decide) with h961 | h961
              · rcases m.htr 2 3 5 (by decide) (by decide) with h962 | h962
                · rcases h0bigk with h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h1, hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h718, h961, hlam, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h718, hlam, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h918, hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h920, hlam, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h957, hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, h918, hc12, hc23, hlam, hphi, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, h718, h918, h961, hc12, hc23, hlam, hphi, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, h718, h918, hc12, hc23, hlam, hphi, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, h920, hc12, hc24, hlam, hphi, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h959, hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, h718, h918, h959, hc12, hc23, hlam, hphi, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h0, h957, hc12, hc25, hlam, hphi, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h960, hlam, p963_0]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [h961, hlam, p963_1]
                  · have p963_0 := h963c.1
                    have p963_1 := h963c.2.1
                    have p963_2 := h963c.2.2.1
                    have p963_3 := h963c.2.2.2
                    linarith only [hlam, p963_0]
                · linarith only [h918, h960, h962, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                · rcases h0bigk with h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h1, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h718, hlam, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h918, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h920, hlam, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h957, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h918, hc01, hc23, hlam, hphi, ht12, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, h918, hc12, hc23, hlam, hphi, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, h918, h920, hc12, hc23, hlam, hphi, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, h718, h918, hc12, hc23, hlam, hphi, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, h920, hc12, hc24, hlam, hphi, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h959, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h961, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, h957, h990, hc12, hc23, hlam, hphi, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h960, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h961, hc04, hc45, hlam, hphi, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                · linarith only [h918, h960, h990, hlam]
            · linarith only [h959, h960, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1019 | h1019
            · linarith only [h1019, h959, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1021 | h1021
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1022 | h1022
                · linarith only [h0, h1, h1019, h1022, hc12, hc23, hlam, hphi]
                · rcases h0bigk with h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, h1, h918, hc12, hc23, hlam, hphi, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h1, hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h1, h1019, h1021, hlam, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h718, hlam, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h918, hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h920, hlam, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h957, hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h1022, h918, hc01, hc35, hlam, hphi, ht12, ht23, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, h1022, h918, hc12, hc35, hlam, hphi, ht23, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h959, hlam, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h1019, hlam, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, h920, hc12, hc24, hlam, hphi, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h959, hc34, hlam, hphi, p1024_1, u3ehi0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [hlam, p1024_0]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, h1, h1019, h959, hc12, hc34, hlam, hphi, ht23, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, h1022, h957, hc12, hc35, hlam, hphi, ht23, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h0, h1, h1022, h957, hc12, hc35, hlam, hphi, ht23, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [h1021, hlam, p1024_1]
                  · have p1024_0 := h1024c.1
                    have p1024_1 := h1024c.2.1
                    have p1024_2 := h1024c.2.2.1
                    have p1024_3 := h1024c.2.2.2
                    linarith only [hlam, p1024_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1050 | h1050
                · linarith only [h0, h1, h1019, h1050, hc12, hc23, hlam, hphi]
                · rcases h0bigk with h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h1, hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h1, h959, hlam, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h718, hlam, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h918, hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h920, hlam, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h957, hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h1021, h959, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, h1021, h959, hc12, hc45, hlam, hphi, ht23, ht34, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h959, hlam, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h1019, hlam, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, h1021, hc12, hc45, hlam, hphi, ht23, ht34, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, h1021, hc12, hc45, hlam, hphi, ht23, ht34, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h1021, hc45, hlam, hphi, ht34, p1052_1, u3ehi0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h1021, hlam, p1052_0]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, h957, hc12, hc25, hlam, hphi, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h0, h1, h1019, hc12, hc35, hlam, hphi, ht23, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [h1021, hc04, hc45, hlam, hphi, p1052_1]
                  · have p1052_0 := h1052c.1
                    have p1052_1 := h1052c.2.1
                    have p1052_2 := h1052c.2.2.1
                    have p1052_3 := h1052c.2.2.2
                    linarith only [hlam, p1052_0]

set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
