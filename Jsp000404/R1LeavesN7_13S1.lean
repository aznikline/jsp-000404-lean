import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h591 | h591
  · rcases m.htr 1 2 5 (by decide) (by decide) with h592 | h592
    · rcases m.htr 1 3 4 (by decide) (by decide) with h593 | h593
      · rcases m.htr 1 3 5 (by decide) (by decide) with h594 | h594
        · rcases m.htr 1 4 5 (by decide) (by decide) with h595 | h595
          · rcases m.htr 2 3 4 (by decide) (by decide) with h596 | h596
            · rcases m.htr 2 3 5 (by decide) (by decide) with h597 | h597
              · rcases m.htr 2 4 5 (by decide) (by decide) with h598 | h598
                · linarith only [h0, h10, h4, h591, h598, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h4, h591, h595, h598, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h591, h596, h597, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h591, h596, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
            · rcases m.htr 2 3 5 (by decide) (by decide) with h604 | h604
              · rcases m.htr 2 4 5 (by decide) (by decide) with h605 | h605
                · linarith only [h10, h591, h595, h605, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                  · linarith only [h0, h10, h4, h591, h595, h603, h607, hc01, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases h2bigk with h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, h592, h605, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, h10, h592, h603, h605, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      rcases p609_3 (m.d 0 2) (by simp) with h613 | h613
                      · rcases p609_3 (m.d 1 2) (by simp) with h614 | h614
                        · linarith only [h0, h614, hlam]
                        · linarith only [h591, h614, hlam]
                      · linarith only [h613, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      rcases p609_3 (m.d 0 2) (by simp) with h618 | h618
                      · rcases p609_3 (m.d 1 2) (by simp) with h619 | h619
                        · linarith only [h0, h619, hlam]
                        · linarith only [h592, h619, hlam]
                      · linarith only [h618, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, hlam, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h10, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h10, h603, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, h10, h4, h603, h605, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h4, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, h4, h603, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h0, h4, h603, h605, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h5, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h591, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h603, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h605, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h6, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h592, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h604, hlam, p609_0]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [h592, h603, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p609_1]
                    · have p609_0 := h609c.1
                      have p609_1 := h609c.2.1
                      have p609_2 := h609c.2.2.1
                      have p609_3 := h609c.2.2.2
                      linarith only [hlam, p609_0]
              · linarith only [h0, h10, h4, h591, h603, h604, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h592, h603, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h10, h592, h594, hlam]
      · linarith only [h10, h591, h593, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h647 | h647
      · rcases m.htr 1 3 5 (by decide) (by decide) with h648 | h648
        · rcases m.htr 1 4 5 (by decide) (by decide) with h649 | h649
          · linarith only [h591, h592, h649, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h651 | h651
            · rcases m.htr 2 3 5 (by decide) (by decide) with h652 | h652
              · rcases m.htr 2 4 5 (by decide) (by decide) with h653 | h653
                · linarith only [h591, h592, h649, h652, h653, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h655 | h655
                  · linarith only [h591, h592, h651, h653, h655, hlam]
                  · rcases h2bigk with h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, h591, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, h10, h591, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      rcases p657_3 (m.d 0 2) (by simp) with h661 | h661
                      · rcases p657_3 (m.d 1 2) (by simp) with h662 | h662
                        · linarith only [h0, h662, hlam]
                        · linarith only [h591, h662, hlam]
                      · linarith only [h661, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, h591, h592, h651, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, hlam, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h10, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h592, h651, h652, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h592, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h4, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, h4, h651, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h5, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h591, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h651, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h653, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h6, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h591, h651, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h652, hlam, p657_0]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [h0, h4, h651, h653, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p657_1]
                    · have p657_0 := h657c.1
                      have p657_1 := h657c.2.1
                      have p657_2 := h657c.2.2.1
                      have p657_3 := h657c.2.2.2
                      linarith only [hlam, p657_0]
              · linarith only [h0, h10, h4, h591, h651, h652, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h591, h651, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h689 | h689
          · linarith only [h591, h592, h689, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h691 | h691
            · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
              · linarith only [h0, h10, h4, h591, h648, h691, h692, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h591, h691, h692, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h591, h691, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h591, h647, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h697 | h697
    · rcases m.htr 1 3 4 (by decide) (by decide) with h698 | h698
      · rcases m.htr 1 3 5 (by decide) (by decide) with h699 | h699
        · rcases m.htr 1 4 5 (by decide) (by decide) with h700 | h700
          · rcases m.htr 2 3 4 (by decide) (by decide) with h701 | h701
            · rcases m.htr 2 3 5 (by decide) (by decide) with h702 | h702
              · rcases m.htr 2 4 5 (by decide) (by decide) with h703 | h703
                · rcases m.htr 3 4 5 (by decide) (by decide) with h704 | h704
                  · rcases h2bigk with h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c | h705c
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, h697, h702, h704, hc01, hc45, hlam, hphi, ht0b, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, h10, h697, h702, h704, hc01, hc45, hlam, hphi, ht0b, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, h591, h697, h702, h704, hc01, hc45, hlam, hphi, ht0b, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      rcases p705_3 (m.d 0 2) (by simp) with h710 | h710
                      · rcases p705_3 (m.d 1 2) (by simp) with h711 | h711
                        · linarith only [h0, h711, hlam]
                        · linarith only [h697, h711, hlam]
                      · linarith only [h710, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, hlam, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h10, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h591, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h591, h701, h702, h704, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h4, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, h4, h702, h704, hc01, hc45, hlam, hphi, ht0b, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h5, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h697, h702, h704, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h701, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h0, h4, h701, h702, h704, hc01, hc45, hlam, hphi, ht0b, ht5b, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h6, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h697, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h702, hlam, p705_0]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [h703, hlam, p705_1]
                    · have p705_0 := h705c.1
                      have p705_1 := h705c.2.1
                      have p705_2 := h705c.2.2.1
                      have p705_3 := h705c.2.2.2
                      linarith only [hlam, p705_0]
                  · linarith only [h0, h10, h4, h697, h703, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h3, h591, h697, h700, h703, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h591, h697, h701, h702, h8, hc03, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h4, h697, h7, h701, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h591, h697, h700, hlam]
        · linarith only [h591, h697, h698, h699, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h741 | h741
        · rcases m.htr 1 4 5 (by decide) (by decide) with h742 | h742
          · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
            · linarith only [h0, h4, h698, h741, h743, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h4, h697, h7, h743, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h10, h697, h698, h742, hlam]
        · linarith only [h10, h697, h741, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h748 | h748
      · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
        · rcases m.htr 1 4 5 (by decide) (by decide) with h750 | h750
          · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
            · rcases m.htr 2 3 5 (by decide) (by decide) with h752 | h752
              · rcases m.htr 2 4 5 (by decide) (by decide) with h753 | h753
                · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                  · rcases h2bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      rcases p755_3 (m.d 0 2) (by simp) with h757 | h757
                      · rcases p755_3 (m.d 1 2) (by simp) with h758 | h758
                        · linarith only [h0, h758, hlam]
                        · rcases p755_3 (m.d 2 3) (by simp) with h760 | h760
                          · linarith only [h4, h760, hlam]
                          · linarith only [h10, h760, hlam]
                      · linarith only [h0, h757, hlam]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h0, h10, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h0, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h0, hlam, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h10, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h591, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h697, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h4, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h0, h4, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h0, h4, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h5, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h751, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h0, h4, h697, h751, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h6, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h752, hlam, p755_0]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [h753, hlam, p755_1]
                    · have p755_0 := h755c.1
                      have p755_1 := h755c.2.1
                      have p755_2 := h755c.2.2.1
                      have p755_3 := h755c.2.2.2
                      linarith only [hlam, p755_0]
                  · rcases h2bigk with h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c | h787c
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      rcases p787_3 (m.d 0 2) (by simp) with h789 | h789
                      · rcases p787_3 (m.d 1 2) (by simp) with h790 | h790
                        · linarith only [h0, h790, hlam]
                        · rcases p787_3 (m.d 2 3) (by simp) with h792 | h792
                          · linarith only [h4, h792, hlam]
                          · linarith only [h10, h792, hlam]
                      · linarith only [h0, h789, hlam]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h10, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, hlam, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h10, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h591, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h697, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h4, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h4, h591, h750, h754, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h4, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h5, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h751, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h0, h4, h697, h751, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h6, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h752, hlam, p787_0]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [h753, hlam, p787_1]
                    · have p787_0 := h787c.1
                      have p787_1 := h787c.2.1
                      have p787_2 := h787c.2.2.1
                      have p787_3 := h787c.2.2.2
                      linarith only [hlam, p787_0]
                · linarith only [h1, h591, h748, h750, h753, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h10, h749, h752, hlam]
            · linarith only [h10, h748, h751, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h822 | h822
            · rcases m.htr 2 3 5 (by decide) (by decide) with h823 | h823
              · rcases m.htr 2 4 5 (by decide) (by decide) with h824 | h824
                · rcases m.htr 3 4 5 (by decide) (by decide) with h825 | h825
                  · linarith only [h748, h750, h825, hlam]
                  · rcases h2bigk with h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      rcases p827_3 (m.d 0 2) (by simp) with h829 | h829
                      · rcases p827_3 (m.d 1 2) (by simp) with h830 | h830
                        · linarith only [h0, h830, hlam]
                        · rcases p827_3 (m.d 2 3) (by simp) with h832 | h832
                          · linarith only [h4, h832, hlam]
                          · linarith only [h10, h832, hlam]
                      · linarith only [h0, h829, hlam]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h0, h591, h750, h822, h824, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h0, h591, h750, h824, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h0, hlam, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h10, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h591, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h697, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h4, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h0, h4, h591, h750, h824, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h0, h4, h697, hc01, hc15, hlam, hphi, ht0b, ht5b, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h5, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h822, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h0, h4, h697, h822, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h6, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h823, hlam, p827_0]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [h824, hlam, p827_1]
                    · have p827_0 := h827c.1
                      have p827_1 := h827c.2.1
                      have p827_2 := h827c.2.2.1
                      have p827_3 := h827c.2.2.2
                      linarith only [hlam, p827_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h859 | h859
                  · linarith only [h591, h824, h859, hc12, hc34, hlam, hphi, ht23]
                  · rcases h2bigk with h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c | h861c
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      rcases p861_3 (m.d 0 2) (by simp) with h863 | h863
                      · rcases p861_3 (m.d 1 2) (by simp) with h864 | h864
                        · linarith only [h0, h864, hlam]
                        · rcases p861_3 (m.d 2 3) (by simp) with h866 | h866
                          · linarith only [h4, h866, hlam]
                          · linarith only [h10, h866, hlam]
                      · linarith only [h0, h863, hlam]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h0, h10, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h0, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h0, hlam, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h10, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h591, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h697, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h4, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h0, h4, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h0, h4, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h5, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h822, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h824, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h6, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h823, hlam, p861_0]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [h0, h4, h591, h7, h824, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p861_1]
                    · have p861_0 := h861c.1
                      have p861_1 := h861c.2.1
                      have p861_2 := h861c.2.2.1
                      have p861_3 := h861c.2.2.2
                      linarith only [hlam, p861_0]
              · linarith only [h10, h749, h823, hlam]
            · linarith only [h10, h748, h822, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h895 | h895
          · linarith only [h748, h749, h895, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h897 | h897
            · rcases m.htr 2 3 5 (by decide) (by decide) with h898 | h898
              · linarith only [h0, h4, h748, h749, h898, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h900 | h900
                · linarith only [h0, h4, h8, h895, h897, h898, h900, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h902 | h902
                  · linarith only [h591, h748, h900, h902, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h2bigk with h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c | h904c
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      rcases p904_3 (m.d 0 2) (by simp) with h906 | h906
                      · rcases p904_3 (m.d 1 2) (by simp) with h907 | h907
                        · linarith only [h0, h907, hlam]
                        · rcases p904_3 (m.d 2 3) (by simp) with h909 | h909
                          · linarith only [h4, h909, hlam]
                          · linarith only [h10, h909, hlam]
                      · linarith only [h0, h906, hlam]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h591, h897, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h0, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h0, hlam, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h10, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h591, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h697, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h4, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h7, h898, h9, h902, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h0, h4, h591, h7, h898, h9, h902, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h898, hlam, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h5, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h897, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h900, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h6, hlam, p904_0]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h0, h10, h4, h7, h898, h9, h902, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [h0, h4, h591, h7, h898, h9, h902, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p904_1]
                    · have p904_0 := h904c.1
                      have p904_1 := h904c.2.1
                      have p904_2 := h904c.2.2.1
                      have p904_3 := h904c.2.2.2
                      linarith only [hlam, p904_0]
            · linarith only [h1, h10, h748, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h937 | h937
        · rcases m.htr 1 4 5 (by decide) (by decide) with h938 | h938
          · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
            · linarith only [h0, h4, h748, h937, h939, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h941 | h941
              · rcases m.htr 2 4 5 (by decide) (by decide) with h942 | h942
                · rcases m.htr 3 4 5 (by decide) (by decide) with h943 | h943
                  · rcases h2bigk with h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c | h944c
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      rcases p944_3 (m.d 0 2) (by simp) with h946 | h946
                      · rcases p944_3 (m.d 1 2) (by simp) with h947 | h947
                        · linarith only [h0, h947, hlam]
                        · rcases p944_3 (m.d 2 3) (by simp) with h949 | h949
                          · linarith only [h4, h949, hlam]
                          · linarith only [h10, h949, hlam]
                      · linarith only [h0, h946, hlam]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h697, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h697, h939, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, hlam, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h10, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h591, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h697, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h4, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h939, hlam, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h697, h7, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h5, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h7, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h7, h939, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h0, h4, h697, h7, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h6, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h941, hc12, hc23, hlam, hphi, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h941, hlam, p944_0]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [h942, hlam, p944_1]
                    · have p944_0 := h944c.1
                      have p944_1 := h944c.2.1
                      have p944_2 := h944c.2.2.1
                      have p944_3 := h944c.2.2.2
                      linarith only [hlam, p944_0]
                  · linarith only [h10, h939, h943, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h10, h591, h937, h938, h939, h942, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h10, h937, h941, hlam]
          · linarith only [h748, h937, h938, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h980 | h980
          · rcases m.htr 2 3 4 (by decide) (by decide) with h981 | h981
            · rcases m.htr 2 3 5 (by decide) (by decide) with h982 | h982
              · rcases m.htr 2 4 5 (by decide) (by decide) with h983 | h983
                · rcases m.htr 3 4 5 (by decide) (by decide) with h984 | h984
                  · rcases h2bigk with h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      rcases p985_3 (m.d 0 2) (by simp) with h987 | h987
                      · rcases p985_3 (m.d 1 2) (by simp) with h988 | h988
                        · linarith only [h0, h988, hlam]
                        · rcases p985_3 (m.d 2 3) (by simp) with h990 | h990
                          · linarith only [h4, h990, hlam]
                          · linarith only [h10, h990, hlam]
                      · linarith only [h0, h987, hlam]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h0, h10, h937, h981, h984, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h0, h10, h937, h982, h983, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h0, h10, h937, h982, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h0, hlam, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h10, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h591, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h697, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h4, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h0, h10, h4, h937, h982, h983, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h0, h10, h4, h937, h982, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h5, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h981, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h0, h10, h4, h937, h981, h982, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h6, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h982, hlam, p985_0]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [h983, hlam, p985_1]
                    · have p985_0 := h985c.1
                      have p985_1 := h985c.2.1
                      have p985_2 := h985c.2.2.1
                      have p985_3 := h985c.2.2.2
                      linarith only [hlam, p985_0]
                  · linarith only [h10, h2, h748, h980, h984, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h591, h980, h983, hlam]
              · linarith only [h748, h8, h980, h981, h982, hc03, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1020 | h1020
              · linarith only [h10, h1020, h937, h981, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1022 | h1022
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1023 | h1023
                  · rcases h2bigk with h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      rcases p1024_3 (m.d 0 2) (by simp) with h1026 | h1026
                      · rcases p1024_3 (m.d 1 2) (by simp) with h1027 | h1027
                        · linarith only [h0, h1027, hlam]
                        · rcases p1024_3 (m.d 2 3) (by simp) with h1029 | h1029
                          · linarith only [h1029, h4, hlam]
                          · linarith only [h10, h1029, hlam]
                      · linarith only [h0, h1026, hlam]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h0, h10, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h0, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h0, hlam, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h10, hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h591, hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h697, hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h4, hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h981, hlam, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h1020, hlam, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h5, hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h0, h4, h7, h981, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h0, h10, h1020, h4, h7, h981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h6, hlam, p1024_0]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h0, h10, h1020, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [h1022, hlam, p1024_1]
                    · have p1024_0 := h1024c.1
                      have p1024_1 := h1024c.2.1
                      have p1024_2 := h1024c.2.2.1
                      have p1024_3 := h1024c.2.2.2
                      linarith only [hlam, p1024_0]
                  · linarith only [h1023, h2, h591, h980, h981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1022, h591, h980, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1058 | h1058
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1059 | h1059
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1060 | h1060
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1061 | h1061
                  · linarith only [h0, h10, h1058, h1061, h4, h748, h980, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h10, h1060, h1061, h748, hc12, hc24, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1064 | h1064
                  · linarith only [h0, h1060, h1064, h4, h591, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h2bigk with h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      rcases p1066_3 (m.d 0 2) (by simp) with h1068 | h1068
                      · rcases p1066_3 (m.d 1 2) (by simp) with h1069 | h1069
                        · linarith only [h0, h1069, hlam]
                        · rcases p1066_3 (m.d 2 3) (by simp) with h1071 | h1071
                          · linarith only [h1071, h4, hlam]
                          · linarith only [h10, h1071, hlam]
                      · linarith only [h0, h1068, hlam]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h0, h1059, h937, hc01, hc15, hlam, hphi, ht0b, ht5b, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h0, h10, h1058, h748, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h0, hlam, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h10, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h591, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h697, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h4, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h0, h10, h1058, h4, h748, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h0, h4, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h5, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h1058, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h1060, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h6, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h1059, hlam, p1066_0]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [h0, h1060, h4, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1066_1]
                    · have p1066_0 := h1066c.1
                      have p1066_1 := h1066c.2.1
                      have p1066_2 := h1066c.2.2.1
                      have p1066_3 := h1066c.2.2.2
                      linarith only [hlam, p1066_0]
              · linarith only [h0, h10, h1058, h1059, h4, h748, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1099 | h1099
              · linarith only [h10, h1058, h1099, h937, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1101 | h1101
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1102 | h1102
                  · rcases h2bigk with h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      rcases p1103_3 (m.d 0 2) (by simp) with h1105 | h1105
                      · rcases p1103_3 (m.d 1 2) (by simp) with h1106 | h1106
                        · linarith only [h0, h1106, hlam]
                        · rcases p1103_3 (m.d 2 3) (by simp) with h1108 | h1108
                          · linarith only [h1108, h4, hlam]
                          · linarith only [h10, h1108, hlam]
                      · linarith only [h0, h1105, hlam]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h0, h10, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h0, h591, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h0, h697, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h0, hlam, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h10, hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h591, hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h697, hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h4, hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hc12, hc23, hlam, hphi, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h1058, hlam, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h1099, hlam, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h5, hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hc12, hc24, hlam, hphi, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h0, h1058, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h0, h10, h1058, h1099, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h6, hlam, p1103_0]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hc12, hc25, hlam, hphi, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h0, h10, h1099, h1102, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [h1101, hlam, p1103_1]
                    · have p1103_0 := h1103c.1
                      have p1103_1 := h1103c.2.1
                      have p1103_2 := h1103c.2.2.1
                      have p1103_3 := h1103c.2.2.2
                      linarith only [hlam, p1103_0]
                  · linarith only [h0, h10, h1058, h1102, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1136 | h1136
                  · linarith only [h0, h1101, h1136, h4, h591, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h10, h1058, h1136, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5328000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9 h10
  · exact r1l7_22_13_15_H_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9 h10

end R2N4
