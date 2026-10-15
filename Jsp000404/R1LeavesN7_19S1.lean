import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5556000 in
theorem r1l7_21_14_H_I_L_I_s4_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h567 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 5 (by decide) (by decide) with h568 | h568
  · rcases m.htr 1 3 4 (by decide) (by decide) with h569 | h569
    · rcases m.htr 1 3 5 (by decide) (by decide) with h570 | h570
      · rcases m.htr 1 4 5 (by decide) (by decide) with h571 | h571
        · rcases m.htr 2 3 4 (by decide) (by decide) with h572 | h572
          · rcases m.htr 2 4 5 (by decide) (by decide) with h573 | h573
            · rcases m.htr 3 4 5 (by decide) (by decide) with h574 | h574
              · rcases h1bigk with h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h567, h572, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h567, h572, h574, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h567, h572, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  rcases p575_3 (m.d 0 1) (by simp) with h580 | h580
                  · rcases p575_3 (m.d 1 2) (by simp) with h581 | h581
                    · linarith only [h0, h581, hlam]
                    · linarith only [h568, h581, hlam]
                  · linarith only [h580, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h0, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h7, hlam, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h567, h572, h574, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h7, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h1, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h1, h567, h572, h574, hc01, hc45, hlam, hphi, ht0b, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h1, h568, hc01, hc25, hlam, hphi, ht0b, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h2, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h567, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h569, hlam, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h2, h568, hc01, hc25, hlam, hphi, ht0b, ht5b, p575_1]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h3, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h568, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h570, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [h571, hlam, p575_0]
                · have p575_0 := h575c.1
                  have p575_1 := h575c.2.1
                  have p575_2 := h575c.2.2.1
                  have p575_3 := h575c.2.2.2
                  linarith only [hlam, p575_0]
              · linarith only [h567, h573, h574, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h606 | h606
              · linarith only [h1, h569, h573, h606, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h1bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h567, h572, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h567, h572, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h571, h572, h573, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h571, h572, h573, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h0, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h7, hlam, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h571, h572, h573, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h1, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h1, h567, h572, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h1, h571, h572, h573, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h2, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h567, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h569, hlam, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h567, h571, h572, h573, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p608_1]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h3, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h568, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h570, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [h571, hlam, p608_0]
                · have p608_0 := h608c.1
                  have p608_1 := h608c.2.1
                  have p608_2 := h608c.2.2.1
                  have p608_3 := h608c.2.2.2
                  linarith only [hlam, p608_0]
          · linarith only [h1, h5, h567, h572, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
          · rcases m.htr 2 4 5 (by decide) (by decide) with h636 | h636
            · linarith only [h567, h571, h636, h7, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h638 | h638
              · linarith only [h568, h571, h635, h636, h638, hlam]
              · rcases h1bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h567, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h567, h635, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  rcases p640_3 (m.d 0 1) (by simp) with h644 | h644
                  · rcases p640_3 (m.d 1 2) (by simp) with h645 | h645
                    · linarith only [h0, h645, hlam]
                    · linarith only [h567, h645, hlam]
                  · linarith only [h644, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  rcases p640_3 (m.d 0 1) (by simp) with h649 | h649
                  · rcases p640_3 (m.d 1 2) (by simp) with h650 | h650
                    · linarith only [h0, h650, hlam]
                    · linarith only [h568, h650, hlam]
                  · linarith only [h649, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h0, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h7, hlam, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h567, h571, h635, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h1, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h1, h567, h635, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h1, h567, h571, h635, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h2, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h567, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h569, hlam, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h571, hlam, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h3, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h568, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h570, hlam, p640_0]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [h3, h567, h635, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p640_1]
                · have p640_0 := h640c.1
                  have p640_1 := h640c.2.1
                  have p640_2 := h640c.2.2.1
                  have p640_3 := h640c.2.2.2
                  linarith only [hlam, p640_0]
          · linarith only [h1, h5, h568, h635, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h568, h570, h7, hlam]
    · linarith only [h567, h569, h7, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
    · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
      · rcases m.htr 1 4 5 (by decide) (by decide) with h679 | h679
        · linarith only [h567, h568, h679, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h681 | h681
          · rcases m.htr 2 4 5 (by decide) (by decide) with h682 | h682
            · linarith only [h567, h679, h682, h7, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h684 | h684
              · linarith only [h567, h568, h681, h682, h684, hlam]
              · rcases h1bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h567, h681, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h678, hc01, hc35, hlam, hphi, ht0b, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  rcases p686_3 (m.d 0 1) (by simp) with h690 | h690
                  · rcases p686_3 (m.d 1 2) (by simp) with h691 | h691
                    · linarith only [h0, h691, hlam]
                    · linarith only [h567, h691, hlam]
                  · linarith only [h690, hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h567, h568, h681, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h0, hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h7, hlam, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h4, h568, h6, h682, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h568, hlam, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h1, hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h567, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h1, h567, h681, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h1, h567, h568, h681, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h2, hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h567, hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h677, hlam, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h679, hlam, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h3, hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h567, h681, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h678, hlam, p686_0]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [h4, h567, h568, h6, h681, h682, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p686_1]
                · have p686_0 := h686c.1
                  have p686_1 := h686c.2.1
                  have p686_2 := h686c.2.2.1
                  have p686_3 := h686c.2.2.2
                  linarith only [hlam, p686_0]
          · linarith only [h1, h5, h567, h681, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h717 | h717
        · linarith only [h567, h678, h7, h717, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h719 | h719
          · rcases m.htr 2 4 5 (by decide) (by decide) with h720 | h720
            · linarith only [h567, h678, h7, h717, h720, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h722 | h722
              · linarith only [h1, h5, h567, h568, h720, h722, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h1bigk with h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h567, h719, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h567, h7, h719, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  rcases p724_3 (m.d 0 1) (by simp) with h728 | h728
                  · rcases p724_3 (m.d 1 2) (by simp) with h729 | h729
                    · linarith only [h0, h729, hlam]
                    · linarith only [h567, h729, hlam]
                  · linarith only [h728, hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h567, h678, h7, h719, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h0, hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h7, hlam, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h7, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h568, hlam, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h1, hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h567, h678, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h0, h4, h567, h6, h678, h719, h722, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h678, hlam, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h2, hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h567, hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h677, hlam, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h717, hlam, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h3, hlam, p724_0]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h3, h567, h719, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h0, h4, h6, h678, h722, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [h0, h4, h567, h6, h678, h719, h722, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1]
                · have p724_0 := h724c.1
                  have p724_1 := h724c.2.1
                  have p724_2 := h724c.2.2.1
                  have p724_3 := h724c.2.2.2
                  linarith only [hlam, p724_0]
          · linarith only [h1, h5, h567, h7, h719, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h567, h677, h7, hlam]

end R2N4
