import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h556 | h556
  · rcases m.htr 1 2 5 (by decide) (by decide) with h557 | h557
    · rcases m.htr 1 3 4 (by decide) (by decide) with h558 | h558
      · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
        · rcases m.htr 1 4 5 (by decide) (by decide) with h560 | h560
          · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
            · rcases m.htr 2 3 5 (by decide) (by decide) with h562 | h562
              · rcases m.htr 2 4 5 (by decide) (by decide) with h563 | h563
                · linarith only [h0, h10, h4, h556, h563, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h4, h556, h560, h563, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h557, h562, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h10, h557, h561, h7, hc03, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
            · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
              · rcases m.htr 2 4 5 (by decide) (by decide) with h570 | h570
                · linarith only [h556, h560, h570, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h572 | h572
                  · linarith only [h556, h560, h568, h572, hlam]
                  · rcases h0bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h0, h557, h568, h570, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h10, h4, h557, h568, h570, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h556, h560, h568, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h556, h560, h568, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h0, hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h10, h4, h557, h568, h570, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h0, h556, h560, h568, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h0, h556, h560, h568, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h1, hlam, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h4, hlam, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h556, h560, h568, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h0, h4, h556, h560, h568, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h2, hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h5, hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h7, hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h556, h560, h568, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h3, hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h6, hlam, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h8, hlam, p574_0]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [h9, hlam, p574_1]
                    · have p574_0 := h574c.1
                      have p574_1 := h574c.2.1
                      have p574_2 := h574c.2.2.1
                      have p574_3 := h574c.2.2.2
                      linarith only [hlam, p574_0]
              · linarith only [h0, h10, h4, h557, h569, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h4, h556, h568, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h10, h557, h559, hlam]
      · linarith only [h10, h556, h558, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h604 | h604
      · rcases m.htr 1 3 5 (by decide) (by decide) with h605 | h605
        · rcases m.htr 1 4 5 (by decide) (by decide) with h606 | h606
          · linarith only [h556, h557, h606, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
            · rcases m.htr 2 3 5 (by decide) (by decide) with h609 | h609
              · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
                · linarith only [h556, h557, h6, h606, h610, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h612 | h612
                  · linarith only [h556, h557, h608, h610, h612, hlam]
                  · rcases h0bigk with h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h4, h557, h610, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h556, h557, h610, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h556, h557, h610, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h3, h556, h557, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
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
                      linarith only [h556, h557, h610, h7, h9, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h0, h556, h557, h610, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h0, h3, h556, h557, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h1, hlam, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h4, hlam, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h556, h557, h610, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h0, h4, h556, h557, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h2, hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h5, hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h7, hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h556, h557, h6, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h3, hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h6, hlam, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h8, hlam, p614_0]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [h9, hlam, p614_1]
                    · have p614_0 := h614c.1
                      have p614_1 := h614c.2.1
                      have p614_2 := h614c.2.2.1
                      have p614_3 := h614c.2.2.2
                      linarith only [hlam, p614_0]
              · linarith only [h0, h10, h4, h556, h608, h609, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h556, h608, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
          · linarith only [h556, h557, h642, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h644 | h644
            · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
              · linarith only [h0, h10, h4, h556, h605, h644, h645, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h4, h556, h644, h645, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h4, h556, h644, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h556, h604, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
    · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
      · rcases m.htr 1 3 5 (by decide) (by decide) with h652 | h652
        · rcases m.htr 1 4 5 (by decide) (by decide) with h653 | h653
          · rcases m.htr 2 3 4 (by decide) (by decide) with h654 | h654
            · rcases m.htr 2 3 5 (by decide) (by decide) with h655 | h655
              · rcases m.htr 2 4 5 (by decide) (by decide) with h656 | h656
                · rcases m.htr 3 4 5 (by decide) (by decide) with h657 | h657
                  · rcases h0bigk with h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h1, h651, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h2, h556, h650, h655, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      rcases p658_3 (m.d 0 1) (by simp) with h663 | h663
                      · rcases p658_3 (m.d 0 2) (by simp) with h664 | h664
                        · linarith only [h0, h664, hlam]
                        · linarith only [h6, h664, hlam]
                      · linarith only [h3, h663, hlam]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h0, hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h5, h556, h650, h655, h657, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h0, h5, h556, h650, h655, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      rcases p658_3 (m.d 0 1) (by simp) with h672 | h672
                      · rcases p658_3 (m.d 0 2) (by simp) with h673 | h673
                        · rcases p658_3 (m.d 0 3) (by simp) with h674 | h674
                          · linarith only [h4, h674, hlam]
                          · linarith only [h674, h8, hlam]
                        · linarith only [h6, h673, hlam]
                      · linarith only [h3, h672, hlam]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h1, hlam, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h4, hlam, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h5, h556, h650, h655, h657, hc03, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      rcases p658_3 (m.d 0 1) (by simp) with h683 | h683
                      · rcases p658_3 (m.d 0 2) (by simp) with h684 | h684
                        · rcases p658_3 (m.d 0 3) (by simp) with h685 | h685
                          · rcases p658_3 (m.d 0 4) (by simp) with h686 | h686
                            · linarith only [h686, h7, hlam]
                            · linarith only [h686, h9, hlam]
                          · linarith only [h685, h8, hlam]
                        · linarith only [h6, h684, hlam]
                      · linarith only [h3, h683, hlam]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h2, hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h5, hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h7, hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      rcases p658_3 (m.d 0 1) (by simp) with h696 | h696
                      · rcases p658_3 (m.d 0 2) (by simp) with h697 | h697
                        · rcases p658_3 (m.d 0 3) (by simp) with h698 | h698
                          · rcases p658_3 (m.d 0 4) (by simp) with h699 | h699
                            · rcases p658_3 (m.d 0 5) (by simp) with h700 | h700
                              · linarith only [h700, h9, hlam]
                              · rcases h1bigk with h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  rcases p702_3 (m.d 0 1) (by simp) with h704 | h704
                                  · rcases p702_3 (m.d 1 2) (by simp) with h705 | h705
                                    · linarith only [h705, hlam, p702_0]
                                    · rcases p702_3 (m.d 1 3) (by simp) with h707 | h707
                                      · linarith only [h1, h707, hlam]
                                      · linarith only [h10, h707, hlam]
                                  · linarith only [h704, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h651, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  rcases p702_3 (m.d 0 1) (by simp) with h712 | h712
                                  · rcases p702_3 (m.d 1 2) (by simp) with h713 | h713
                                    · linarith only [h0, h713, hlam]
                                    · rcases p702_3 (m.d 1 3) (by simp) with h715 | h715
                                      · linarith only [h1, h715, hlam]
                                      · linarith only [h651, h715, hlam]
                                  · linarith only [h712, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h2, h3, hlam, p658_1, p702_2]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h0, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h10, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h556, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h0, h4, h556, h650, h654, h655, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h1, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h0, h10, h4, h650, h655, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h0, h10, h4, h556, h650, h655, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  rcases p702_3 (m.d 0 1) (by simp) with h729 | h729
                                  · rcases p702_3 (m.d 1 2) (by simp) with h730 | h730
                                    · linarith only [h10, h730, hlam]
                                    · linarith only [h650, h730, hlam]
                                  · linarith only [h3, h729, hlam]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h2, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h2, h650, h655, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h651, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  rcases p702_3 (m.d 0 1) (by simp) with h738 | h738
                                  · rcases p702_3 (m.d 1 2) (by simp) with h739 | h739
                                    · linarith only [h556, h739, hlam]
                                    · linarith only [h650, h739, hlam]
                                  · linarith only [h3, h738, hlam]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h3, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h650, hlam, p702_1]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h652, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [h653, hlam, p702_0]
                                · have p702_0 := h702c.1
                                  have p702_1 := h702c.2.1
                                  have p702_2 := h702c.2.2.1
                                  have p702_3 := h702c.2.2.2
                                  linarith only [hlam, p702_0]
                            · linarith only [h699, h9, hlam]
                          · linarith only [h698, h8, hlam]
                        · linarith only [h6, h697, hlam]
                      · linarith only [h3, h696, hlam]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h3, hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h6, hlam, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h8, hlam, p658_0]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [h9, hlam, p658_1]
                    · have p658_0 := h658c.1
                      have p658_1 := h658c.2.1
                      have p658_2 := h658c.2.2.1
                      have p658_3 := h658c.2.2.2
                      linarith only [hlam, p658_0]
                  · linarith only [h0, h10, h4, h650, h656, h657, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h3, h556, h650, h653, h656, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h4, h556, h650, h654, h655, h8, hc02, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h4, h650, h654, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h556, h650, h653, hlam]
        · linarith only [h556, h650, h651, h652, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h763 | h763
        · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
          · rcases m.htr 2 3 4 (by decide) (by decide) with h765 | h765
            · linarith only [h0, h4, h651, h763, h765, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h4, h650, h7, h765, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h10, h650, h651, h764, hlam]
        · linarith only [h10, h650, h763, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h770 | h770
      · rcases m.htr 1 3 5 (by decide) (by decide) with h771 | h771
        · rcases m.htr 1 4 5 (by decide) (by decide) with h772 | h772
          · rcases m.htr 2 3 4 (by decide) (by decide) with h773 | h773
            · rcases m.htr 2 3 5 (by decide) (by decide) with h774 | h774
              · rcases m.htr 2 4 5 (by decide) (by decide) with h775 | h775
                · rcases m.htr 3 4 5 (by decide) (by decide) with h776 | h776
                  · rcases h0bigk with h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c | h777c
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h1, h4, h770, h776, hc01, hc45, hlam, hphi, ht0b, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h1, h770, h776, hc01, hc45, hlam, hphi, ht0b, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h7, h776, hc01, hc45, hlam, hphi, ht0b, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h6, h650, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h0, hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h10, h4, h770, h776, hc02, hc45, hlam, hphi, ht0b, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h0, h5, h556, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h0, h6, h650, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h1, hlam, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h4, hlam, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h5, h556, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h0, h4, h6, h650, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h2, hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h5, hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h7, hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h0, h4, h6, h650, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h3, hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h6, hlam, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h8, hlam, p777_0]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [h9, hlam, p777_1]
                    · have p777_0 := h777c.1
                      have p777_1 := h777c.2.1
                      have p777_2 := h777c.2.2.1
                      have p777_3 := h777c.2.2.2
                      linarith only [hlam, p777_0]
                  · rcases h0bigk with h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h1, h4, h770, h772, h776, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h1, h770, h772, h776, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h2, h772, h776, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h776, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h0, hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h10, h4, h770, h772, h776, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h0, h5, h556, h772, h776, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h0, h776, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h1, hlam, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h4, hlam, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h5, h556, h772, h776, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h0, h4, h776, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h2, hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h5, hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h7, hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h0, h4, h7, h776, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h3, hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h6, hlam, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h8, hlam, p803_0]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [h9, hlam, p803_1]
                    · have p803_0 := h803c.1
                      have p803_1 := h803c.2.1
                      have p803_2 := h803c.2.2.1
                      have p803_3 := h803c.2.2.2
                      linarith only [hlam, p803_0]
                · linarith only [h556, h772, h775, hlam]
              · linarith only [h10, h771, h774, hlam]
            · linarith only [h10, h770, h773, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h832 | h832
            · rcases m.htr 2 3 5 (by decide) (by decide) with h833 | h833
              · rcases m.htr 2 4 5 (by decide) (by decide) with h834 | h834
                · rcases m.htr 3 4 5 (by decide) (by decide) with h835 | h835
                  · linarith only [h770, h772, h835, hlam]
                  · rcases h0bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h4, h556, h772, h832, h834, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h4, h556, h772, h832, h834, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h5, h556, h772, h834, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h556, h772, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h0, hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h4, h556, h772, h832, h834, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h0, h5, h556, h772, h834, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h0, h556, h772, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h1, hlam, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h4, hlam, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h5, h556, h772, h834, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h0, h4, h556, h772, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h2, hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h5, hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h7, hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h0, h4, h556, h7, h772, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h3, hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h6, hlam, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h8, hlam, p837_0]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [h9, hlam, p837_1]
                    · have p837_0 := h837c.1
                      have p837_1 := h837c.2.1
                      have p837_2 := h837c.2.2.1
                      have p837_3 := h837c.2.2.2
                      linarith only [hlam, p837_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h863 | h863
                  · linarith only [h556, h834, h863, hc12, hc34, hlam, hphi, ht23]
                  · rcases h0bigk with h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h1, h4, h771, hc01, hc35, hlam, hphi, ht0b, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h1, h771, hc01, hc35, hlam, hphi, ht0b, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h5, h556, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h556, h834, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h0, hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h0, h1, h771, hc01, hc35, hlam, hphi, ht0b, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h0, h5, h556, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h0, h556, h834, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h1, hlam, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h4, hlam, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h5, h556, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h0, h4, h556, h834, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h2, hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h5, hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h7, hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h556, h834, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h3, hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h6, hlam, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h8, hlam, p865_0]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [h9, hlam, p865_1]
                    · have p865_0 := h865c.1
                      have p865_1 := h865c.2.1
                      have p865_2 := h865c.2.2.1
                      have p865_3 := h865c.2.2.2
                      linarith only [hlam, p865_0]
              · linarith only [h10, h771, h833, hlam]
            · linarith only [h10, h770, h832, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h893 | h893
          · linarith only [h770, h771, h893, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h895 | h895
            · rcases m.htr 2 3 5 (by decide) (by decide) with h896 | h896
              · linarith only [h0, h4, h770, h771, h896, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h898 | h898
                · linarith only [h0, h4, h8, h893, h895, h896, h898, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h900 | h900
                  · linarith only [h1, h770, h898, h900, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c | h902c
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h10, h4, h7, h896, h9, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h10, h7, h770, h896, h9, h900, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h10, h770, h896, h9, h900, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h10, h6, h770, h896, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h0, hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h10, h7, h770, h896, h9, h900, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h0, h10, h770, h896, h9, h900, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h0, h10, h6, h770, h896, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h1, hlam, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h4, hlam, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h10, h770, h896, h9, h900, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h0, h10, h4, h6, h770, h896, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h2, hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h5, hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h7, hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h10, h770, h8, h896, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h3, hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h6, hlam, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h8, hlam, p902_0]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [h9, hlam, p902_1]
                    · have p902_0 := h902c.1
                      have p902_1 := h902c.2.1
                      have p902_2 := h902c.2.2.1
                      have p902_3 := h902c.2.2.2
                      linarith only [hlam, p902_0]
            · linarith only [h10, h770, h771, h8, h895, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h929 | h929
        · rcases m.htr 1 4 5 (by decide) (by decide) with h930 | h930
          · rcases m.htr 2 3 4 (by decide) (by decide) with h931 | h931
            · linarith only [h0, h4, h770, h929, h931, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h933 | h933
              · rcases m.htr 2 4 5 (by decide) (by decide) with h934 | h934
                · rcases m.htr 3 4 5 (by decide) (by decide) with h935 | h935
                  · rcases h0bigk with h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c | h936c
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h1, h4, h929, h935, hc01, hc45, hlam, hphi, ht0b, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h1, h929, h935, hc01, hc45, hlam, hphi, ht0b, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h2, h770, h929, h935, hc01, hc45, hlam, hphi, ht0b, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h6, h650, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h0, hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h4, h650, h933, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h0, h5, h650, h931, h933, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h0, h6, h650, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h1, hlam, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h4, hlam, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h5, h650, h931, h933, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h0, h4, h6, h650, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h2, hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h5, hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h7, hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h6, h650, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h3, hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h6, hlam, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h8, hlam, p936_0]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [h9, hlam, p936_1]
                    · have p936_0 := h936c.1
                      have p936_1 := h936c.2.1
                      have p936_2 := h936c.2.2.1
                      have p936_3 := h936c.2.2.2
                      linarith only [hlam, p936_0]
                  · linarith only [h650, h931, h933, h935, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h0, h10, h4, h556, h7, h929, h930, h931, h934, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h10, h929, h933, hlam]
          · linarith only [h770, h929, h930, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h966 | h966
          · rcases m.htr 2 3 4 (by decide) (by decide) with h967 | h967
            · rcases m.htr 2 3 5 (by decide) (by decide) with h968 | h968
              · rcases m.htr 2 4 5 (by decide) (by decide) with h969 | h969
                · rcases m.htr 3 4 5 (by decide) (by decide) with h970 | h970
                  · rcases h0bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h4, h929, h967, h970, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h2, h7, h966, hc01, hc45, hlam, hphi, ht0b, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h2, h966, hc01, hc45, hlam, hphi, ht0b, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h6, h929, h968, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h0, hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h4, h929, h967, h970, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h0, h5, h929, h968, h969, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h0, h6, h929, h968, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h1, hlam, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h4, hlam, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h5, h929, h968, h969, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h0, h4, h6, h929, h968, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h2, hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h5, hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h7, hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h6, h929, h968, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h3, hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h6, hlam, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h8, hlam, p971_0]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [h9, hlam, p971_1]
                    · have p971_0 := h971c.1
                      have p971_1 := h971c.2.1
                      have p971_2 := h971c.2.2.1
                      have p971_3 := h971c.2.2.2
                      linarith only [hlam, p971_0]
                  · linarith only [h0, h10, h5, h556, h770, h966, h970, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h770, h966, h967, h969, hlam]
              · linarith only [h0, h4, h770, h8, h966, h967, h968, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1000 | h1000
              · linarith only [h10, h1000, h929, h967, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1002 | h1002
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1003 | h1003
                  · rcases h0bigk with h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c | h1004c
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h1000, h1003, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h1000, h1003, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h2, h966, hc01, hc45, hlam, hphi, ht0b, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h1000, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h0, hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h1000, h1003, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h0, h1000, h1003, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h0, h1000, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h1, hlam, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h4, hlam, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h1000, h1003, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h0, h1000, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h2, hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h5, hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h7, hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h1000, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h3, hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h6, hlam, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h8, hlam, p1004_0]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [h9, hlam, p1004_1]
                    · have p1004_0 := h1004c.1
                      have p1004_1 := h1004c.2.1
                      have p1004_2 := h1004c.2.2.1
                      have p1004_3 := h1004c.2.2.2
                      linarith only [hlam, p1004_0]
                  · linarith only [h10, h1003, h966, h967, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1002, h556, h966, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1032 | h1032
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1033 | h1033
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1034 | h1034
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1035 | h1035
                  · linarith only [h0, h10, h1032, h1035, h4, h770, h966, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h10, h1032, h1034, h1035, h4, h770, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1038 | h1038
                  · linarith only [h0, h1034, h1038, h4, h556, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h0bigk with h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c | h1040c
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h10, h1032, h5, h7, h770, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h10, h1032, h5, h770, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h10, h1032, h1034, h770, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h0, hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h10, h1032, h5, h7, h770, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h0, h10, h1032, h5, h770, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h0, h10, h1032, h1034, h770, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h1, hlam, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h4, hlam, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h10, h1032, h5, h770, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h0, h10, h1032, h1034, h4, h770, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h2, hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h5, hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h7, hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h10, h1032, h1034, h770, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h3, hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h6, hlam, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h8, hlam, p1040_0]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [h9, hlam, p1040_1]
                    · have p1040_0 := h1040c.1
                      have p1040_1 := h1040c.2.1
                      have p1040_2 := h1040c.2.2.1
                      have p1040_3 := h1040c.2.2.2
                      linarith only [hlam, p1040_0]
              · linarith only [h10, h1032, h1033, h770, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1067 | h1067
              · linarith only [h10, h1032, h1067, h929, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1069 | h1069
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1070 | h1070
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
                      linarith only [h1032, h1069, h4, h7, h966, hc01, hc15, hlam, hphi, ht0b, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h1067, h1070, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h1069, h5, h966, hc01, hc15, hlam, hphi, ht0b, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h1067, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
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
                      linarith only [h1067, h1070, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h0, h1067, h1070, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h0, h1067, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h1, hlam, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h4, hlam, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [hlam, p1071_0]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h1067, h1070, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h0, h1067, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h2, hlam, p1071_0]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h5, hlam, p1071_0]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h7, hlam, p1071_0]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [hlam, p1071_0]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h1067, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h3, hlam, p1071_0]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h6, hlam, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h8, hlam, p1071_0]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [h9, hlam, p1071_1]
                    · have p1071_0 := h1071c.1
                      have p1071_1 := h1071c.2.1
                      have p1071_2 := h1071c.2.2.1
                      have p1071_3 := h1071c.2.2.2
                      linarith only [hlam, p1071_0]
                  · linarith only [h1032, h1069, h1070, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1098 | h1098
                  · linarith only [h0, h1069, h1098, h4, h556, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h10, h1032, h1098, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10

end R2N4
