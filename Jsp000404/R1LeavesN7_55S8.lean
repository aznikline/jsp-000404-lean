import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h534 | h534
  · rcases m.htr 0 2 3 (by decide) (by decide) with h535 | h535
    · rcases m.htr 0 2 5 (by decide) (by decide) with h536 | h536
      · rcases m.htr 0 3 4 (by decide) (by decide) with h537 | h537
        · linarith only [h0, h2, h535, h537, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h539 | h539
          · linarith only [h537, h539, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h541 | h541
            · rcases m.htr 2 3 5 (by decide) (by decide) with h542 | h542
              · linarith only [h0, h2, h535, h539, h542, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases h0bigk with h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c | h544c
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [hlam, p544_0]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p544_1, u3ehi1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h2, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h0, hlam, p544_0]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [hlam, p544_0]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p544_1, u3ehi1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h0, h2, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h0, h1, h2, h539, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p544_1, u3ehi1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h1, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h535, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [hlam, p544_0]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h537, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h539, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h536, h537, h542, hc34, hlam, hphi, p544_1, u3ehi2]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h1, h537, hc34, hlam, hphi, p544_1, u3ehi1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [hlam, p544_0]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h1, h537, h539, hc34, hlam, hphi, p544_1, u3ehi1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h534, hlam, p544_0]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h536, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p544_1, u3ehi1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [h541, hlam, p544_1]
                · have p544_0 := h544c.1
                  have p544_1 := h544c.2.1
                  have p544_2 := h544c.2.2.1
                  have p544_3 := h544c.2.2.2
                  linarith only [hlam, p544_0]
            · linarith only [h1, h2, h541, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h571 | h571
        · linarith only [h2, h534, h535, h536, h571, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h573 | h573
          · linarith only [h571, h573, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h575 | h575
            · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
              · linarith only [h1, h2, h534, h535, h536, h573, h576, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h535, h536, h576, hc35, hlam, hphi, u3ehi2]
            · linarith only [h0, h2, h535, h575, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h580 | h580
      · rcases m.htr 0 3 4 (by decide) (by decide) with h581 | h581
        · linarith only [h1, h2, h581, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h583 | h583
          · linarith only [h581, h583, hc34, hlam, hphi, u3ehi4]
          · linarith only [h535, h580, h583, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h586 | h586
        · linarith only [h1, h2, h586, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h588 | h588
          · linarith only [h586, h588, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h590 | h590
            · rcases m.htr 2 3 5 (by decide) (by decide) with h591 | h591
              · rcases h0bigk with h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p592_1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p592_1, u3ehi0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h2, hlam, p592_1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h1, h2, h588, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p592_1, u3ehi1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h0, hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h535, hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p592_1, u4ehi0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h580, hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h1, hlam, p592_1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h588, h591, hc02, hc23, hlam, hphi, p592_1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h586, hlam, p592_1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h588, hlam, p592_1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h0, h1, h588, h591, hc04, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p592_1, u3ehi1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h0, h1, h586, h588, h591, hc12, hc23, hc34, hlam, hphi, p592_1, u3ehi1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h1, h586, hc34, hlam, hphi, p592_1, u3ehi1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h1, h586, h588, hc34, hlam, hphi, p592_1, u3ehi1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h534, hlam, p592_0]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h0, h1, h2, h534, h588, h591, hc12, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p592_1, u3ehi1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h1, h588, h591, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p592_1, u3ehi1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [h590, hlam, p592_1]
                · have p592_0 := h592c.1
                  have p592_1 := h592c.2.1
                  have p592_2 := h592c.2.2.1
                  have p592_3 := h592c.2.2.2
                  linarith only [hlam, p592_0]
              · rcases h0bigk with h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c | h618c
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p618_1, u3ehi1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h2, hlam, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h0, hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h535, hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p618_1, u4ehi0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h580, hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h1, hlam, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h586, hlam, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h588, hlam, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h0, h586, hc12, hc34, hlam, hphi, ht23, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h586, hc34, hlam, hphi, p618_1, u3ehi0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h0, h580, h586, hc12, hc34, hlam, hphi, ht23, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h534, hlam, p618_0]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h0, h2, h534, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h1, h2, h534, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p618_1, u3ehi1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [h590, hlam, p618_1]
                · have p618_0 := h618c.1
                  have p618_1 := h618c.2.1
                  have p618_2 := h618c.2.2.1
                  have p618_3 := h618c.2.2.2
                  linarith only [hlam, p618_0]
            · linarith only [h1, h2, h590, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h645 | h645
    · rcases m.htr 0 2 5 (by decide) (by decide) with h646 | h646
      · linarith only [h0, h534, h646, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h648 | h648
        · linarith only [h0, h2, h645, h648, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h650 | h650
          · linarith only [h648, h650, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h652 | h652
            · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
              · linarith only [h1, h645, h646, h650, h653, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h645, h646, h653, hc35, hlam, hphi, u3ehi2]
            · linarith only [h0, h2, h645, h652, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h657 | h657
      · linarith only [h1, h534, h645, h657, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h659 | h659
        · linarith only [h1, h2, h659, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h661 | h661
          · linarith only [h659, h661, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h663 | h663
            · rcases m.htr 2 3 5 (by decide) (by decide) with h664 | h664
              · rcases h0bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h534, h661, h664, hc02, hc23, hlam, hphi, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h534, h661, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p665_1, u3ehi0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h2, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h534, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h0, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h645, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p665_1, u4ehi0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h657, hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h1, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h0, h1, h534, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h659, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h661, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h0, h1, h534, h659, h661, h664, hc12, hc23, hc34, hlam, hphi, p665_1, u3ehi1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h1, h659, hc34, hlam, hphi, p665_1, u3ehi1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h1, h534, h659, hc34, hlam, hphi, p665_1, u3ehi1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h1, h661, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p665_1, u3ehi1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h0, h661, h664, hc12, hc23, hlam, hphi, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h1, h661, h664, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p665_1, u3ehi1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [h663, hlam, p665_1]
                · have p665_0 := h665c.1
                  have p665_1 := h665c.2.1
                  have p665_2 := h665c.2.2.1
                  have p665_3 := h665c.2.2.2
                  linarith only [hlam, p665_0]
              · rcases h0bigk with h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c | h691c
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [hlam, p691_0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p691_1, u3ehi1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h2, hlam, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h534, hlam, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h0, hlam, p691_0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [hlam, p691_0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h645, hlam, p691_0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p691_1, u4ehi0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h657, hlam, p691_0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h1, hlam, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h0, h1, h534, h657, hc12, hc25, hlam, hphi, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [hlam, p691_0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h659, hlam, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h661, hlam, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h1, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u3ehi0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h0, h659, hc12, hc34, hlam, hphi, ht23, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h1, h659, hc34, hlam, hphi, p691_1, u3ehi1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [hlam, p691_0]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h1, h534, h659, hc34, hlam, hphi, p691_1, u3ehi1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p691_1, u3ehi1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h0, h657, h664, hc12, hc35, hlam, hphi, ht23, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h1, h657, h664, hc35, hlam, hphi, p691_1, u3ehi1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [h663, hlam, p691_1]
                · have p691_0 := h691c.1
                  have p691_1 := h691c.2.1
                  have p691_2 := h691c.2.2.1
                  have p691_3 := h691c.2.2.2
                  linarith only [hlam, p691_0]
            · linarith only [h1, h2, h663, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1 h2
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1 h2

set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h718 | h718
  · rcases m.htr 0 1 5 (by decide) (by decide) with h719 | h719
    · rcases m.htr 0 2 3 (by decide) (by decide) with h720 | h720
      · linarith only [h0, h1, h720, hlam]
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
                    linarith only [h722, h726, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p727_1, u4ehi0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p727_1]
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
                    linarith only [h720, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h720, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p727_1, u4ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h720, h722, h726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h720, hc01, hc23, hlam, hphi, ht12, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h720, hc02, hc23, hlam, hphi, p727_1]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h720, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p727_1, u4ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h720, h722, h726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h718, hlam, p727_0]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h722, h726, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
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
                    linarith only [h718, h722, h726, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p727_1, u3ehi4]
                  · have p727_0 := h727c.1
                    have p727_1 := h727c.2.1
                    have p727_2 := h727c.2.2.1
                    have p727_3 := h727c.2.2.2
                    linarith only [h719, hlam, p727_0]
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
                · linarith only [h0, h1, h720, h722, h724, h726, hlam]
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
                    linarith only [h720, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h720, h723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h720, h723, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h720, hc01, hc23, hlam, hphi, ht12, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h720, hc02, hc23, hlam, hphi, p755_1]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h720, h723, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h720, h723, h725, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p755_1, u3ehi3]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h718, hlam, p755_0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [h722, h754, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p755_1, u3ehi4]
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
                    linarith only [h719, hlam, p755_0]
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
                    linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p755_1, u4ehi0]
                  · have p755_0 := h755c.1
                    have p755_1 := h755c.2.1
                    have p755_2 := h755c.2.2.1
                    have p755_3 := h755c.2.2.2
                    linarith only [hlam, p755_0]
                · linarith only [h720, h723, h754, hc35, hlam, hphi, u3ehi3]
            · linarith only [h723, h724, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h718, h723, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h784 | h784
          · rcases m.htr 0 3 5 (by decide) (by decide) with h785 | h785
            · rcases m.htr 0 4 5 (by decide) (by decide) with h786 | h786
              · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
                · rcases h0bigk with h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h1, h720, hc02, hc23, hlam, hphi, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h1, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p788_1, u4ehi0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, h1, h722, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h720, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h786, hc02, hlam, hphi, ht0b, ht45, ht5b, p788_1, u4ehi4]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h722, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h720, hc01, hc23, hlam, hphi, ht12, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h720, hc02, hc23, hlam, hphi, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h720, h786, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p788_1, u4ehi4]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h720, h785, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p788_1, u3ehi4]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h718, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, h1, h718, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h784, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h1, h718, h785, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p788_1, u3ehi4]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h719, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, h1, h719, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h785, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h786, hlam, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                · linarith only [h720, h784, h787, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h815 | h815
                · rcases h0bigk with h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c | h816c
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p816_1]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h1, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p816_1, u4ehi0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p816_1]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h0, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h720, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h784, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p816_1, u3ehi3]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h722, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h720, hc01, hc23, hlam, hphi, ht12, p816_1]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h720, hc02, hc23, hlam, hphi, p816_1]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h720, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p816_1, u3ehi3]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h720, h784, h786, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p816_1, u3ehi3]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h718, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h0, h1, h718, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p816_1]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h784, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h786, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h719, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h1, h719, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p816_1]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h785, hlam, p816_0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [h1, h719, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p816_1, u4ehi0]
                  · have p816_0 := h816c.1
                    have p816_1 := h816c.2.1
                    have p816_2 := h816c.2.2.1
                    have p816_3 := h816c.2.2.2
                    linarith only [hlam, p816_0]
                · linarith only [h720, h784, h815, hc35, hlam, hphi, u3ehi3]
            · linarith only [h784, h785, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h718, h784, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h845 | h845
      · linarith only [h0, h1, h845, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h847 | h847
        · linarith only [h0, h719, h847, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h849 | h849
          · rcases m.htr 0 3 5 (by decide) (by decide) with h850 | h850
            · rcases m.htr 0 4 5 (by decide) (by decide) with h851 | h851
              · linarith only [h718, h719, h851, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h853 | h853
                · rcases h0bigk with h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h719, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p854_1]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h1, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h719, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p854_1, u4ehi0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h719, hlam, p854_1]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h0, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h845, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h849, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p854_1, u3ehi3]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h847, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h845, hc01, hc23, hlam, hphi, ht12, p854_1]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h845, hc02, hc23, hlam, hphi, p854_1]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h845, h849, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p854_1, u3ehi3]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h718, h719, h845, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p854_1, u4ehi1]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h718, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h0, h718, h719, h847, hc12, hc25, hlam, hphi, p854_1]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h849, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h851, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h718, hc05, hlam, hphi, ht0b, ht45, ht5b, p854_1, u4ehi0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h0, h847, hc12, hc25, hlam, hphi, p854_1]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h850, hlam, p854_0]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [h849, h851, hc45, hlam, hphi, ht34, p854_1, u3ehi3]
                  · have p854_0 := h854c.1
                    have p854_1 := h854c.2.1
                    have p854_2 := h854c.2.2.1
                    have p854_3 := h854c.2.2.2
                    linarith only [hlam, p854_0]
                · linarith only [h845, h850, h853, hlam]
            · linarith only [h849, h850, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h718, h849, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h883 | h883
    · rcases m.htr 0 2 3 (by decide) (by decide) with h884 | h884
      · linarith only [h0, h1, h884, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h886 | h886
        · rcases m.htr 0 3 4 (by decide) (by decide) with h887 | h887
          · rcases m.htr 0 3 5 (by decide) (by decide) with h888 | h888
            · rcases m.htr 0 4 5 (by decide) (by decide) with h889 | h889
              · rcases m.htr 2 3 5 (by decide) (by decide) with h890 | h890
                · rcases h0bigk with h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h886, h890, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p891_1, u3ehi4]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h1, hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h718, hlam, p891_1]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h718, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p891_1]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h0, hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h884, hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p891_1, u4ehi0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h0, h718, h886, h890, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p891_1, u3ehi4]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h884, hc01, hc23, hlam, hphi, ht12, p891_1]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h884, hc02, hc23, hlam, hphi, p891_1]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h0, h718, h884, h886, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p891_1, u3ehi4]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h884, h886, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p891_1, u3ehi4]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h0, h886, h890, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p891_1, u3ehi4]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h884, h886, h887, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p891_1, u3ehi4]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h887, hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h884, h886, h887, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p891_1, u3ehi4]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h883, hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h886, hlam, p891_1]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h888, hlam, p891_0]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [h889, hlam, p891_1]
                  · have p891_0 := h891c.1
                    have p891_1 := h891c.2.1
                    have p891_2 := h891c.2.2.1
                    have p891_3 := h891c.2.2.2
                    linarith only [hlam, p891_0]
                · linarith only [h884, h887, h890, hc35, hlam, hphi, u3ehi3]
              · linarith only [h718, h883, h889, hlam]
            · linarith only [h887, h888, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h920 | h920
            · linarith only [h887, h920, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h1, h886, h920, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h923 | h923
          · rcases m.htr 0 3 5 (by decide) (by decide) with h924 | h924
            · rcases m.htr 0 4 5 (by decide) (by decide) with h925 | h925
              · rcases m.htr 2 3 5 (by decide) (by decide) with h926 | h926
                · rcases h0bigk with h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h1, hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h718, hlam, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h0, hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h884, hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p927_1, u4ehi0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h886, hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h884, hc01, hc23, hlam, hphi, ht12, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h884, hc02, hc23, hlam, hphi, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h0, h718, h884, hc12, hc23, hlam, hphi, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h884, h924, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p927_1, u3ehi4]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h0, h884, h923, hc12, hc23, hlam, hphi, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h923, hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h884, h923, h924, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p927_1, u3ehi4]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h883, hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h0, h1, h883, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h924, hlam, p927_0]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [h925, hlam, p927_1]
                  · have p927_0 := h927c.1
                    have p927_1 := h927c.2.1
                    have p927_2 := h927c.2.2.1
                    have p927_3 := h927c.2.2.2
                    linarith only [hlam, p927_0]
                · linarith only [h884, h923, h926, hc35, hlam, hphi, u3ehi3]
              · linarith only [h718, h883, h925, hlam]
            · linarith only [h923, h924, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h956 | h956
            · linarith only [h923, h956, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1, h883, h956, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h959 | h959
      · linarith only [h0, h1, h959, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h961 | h961
        · linarith only [h0, h883, h961, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h963 | h963
          · rcases m.htr 0 3 5 (by decide) (by decide) with h964 | h964
            · rcases m.htr 0 4 5 (by decide) (by decide) with h965 | h965
              · rcases m.htr 2 3 5 (by decide) (by decide) with h966 | h966
                · rcases h0bigk with h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c | h967c
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h883, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h1, hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h718, hlam, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h883, hlam, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h959, hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p967_1, u4ehi0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h961, hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h959, hc02, hc23, hlam, hphi, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h959, h965, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p967_1, u4ehi4]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, h883, h959, hc12, hc23, hlam, hphi, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, h959, h963, hc12, hc23, hlam, hphi, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h963, hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, h883, h959, h963, hc12, hc23, hlam, hphi, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h0, h961, h966, hc12, hc23, hlam, hphi, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h964, hlam, p967_0]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [h965, hlam, p967_1]
                  · have p967_0 := h967c.1
                    have p967_1 := h967c.2.1
                    have p967_2 := h967c.2.2.1
                    have p967_3 := h967c.2.2.2
                    linarith only [hlam, p967_0]
                · linarith only [h959, h964, h966, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h994 | h994
                · rcases h0bigk with h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h1, hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h718, hlam, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h883, hlam, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h959, hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p995_1, u4ehi0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h961, hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, h959, hc12, hc23, hlam, hphi, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h959, hc02, hc23, hlam, hphi, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, h718, h959, hc12, hc23, hlam, hphi, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, h883, h959, hc12, hc23, hlam, hphi, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, h961, h965, hc12, hc25, hlam, hphi, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h963, hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h965, hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, h961, hc12, hc25, hlam, hphi, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h0, h961, hc12, hc25, hlam, hphi, p995_1]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h964, hlam, p995_0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [h961, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p995_1, u4ehi0]
                  · have p995_0 := h995c.1
                    have p995_1 := h995c.2.1
                    have p995_2 := h995c.2.2.1
                    have p995_3 := h995c.2.2.2
                    linarith only [hlam, p995_0]
                · linarith only [h959, h964, h994, hlam]
            · linarith only [h963, h964, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1023 | h1023
            · linarith only [h1023, h963, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1025 | h1025
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1026 | h1026
                · linarith only [h0, h1, h1023, h1026, hc12, hc23, hlam, hphi]
                · rcases h0bigk with h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, h1, h959, hc12, hc23, hlam, hphi, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h1, hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h718, hlam, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h883, hlam, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h959, hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h1023, h1025, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1028_1, u3ehi0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h961, hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h1026, h959, hc02, hc35, hlam, hphi, ht23, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h963, hlam, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h1023, hlam, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, h718, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, h963, hc12, hc34, hlam, hphi, ht23, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h963, hc34, hlam, hphi, p1028_1, u3ehi0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [hlam, p1028_0]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, h883, h963, hc12, hc34, hlam, hphi, ht23, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, h1026, h961, hc12, hc35, hlam, hphi, ht23, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h0, h1, h1026, h961, hc12, hc35, hlam, hphi, ht23, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [h1025, hlam, p1028_1]
                  · have p1028_0 := h1028c.1
                    have p1028_1 := h1028c.2.1
                    have p1028_2 := h1028c.2.2.1
                    have p1028_3 := h1028c.2.2.2
                    linarith only [hlam, p1028_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1054 | h1054
                · linarith only [h0, h1, h1023, h1054, hc12, hc23, hlam, hphi]
                · rcases h0bigk with h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h718, hlam, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h883, hlam, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h959, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h963, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1056_1, u3ehi0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h961, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h959, hc02, hc23, hlam, hphi, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h963, hlam, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1023, hlam, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h718, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h1025, hc12, hc45, hlam, hphi, ht23, ht34, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1025, hc45, hlam, hphi, ht34, p1056_1, u3ehi0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1025, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h961, hc12, hc25, hlam, hphi, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h1, h1023, hc12, hc35, hlam, hphi, ht23, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1025, hc45, hlam, hphi, p1056_1, u4ehi0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]

set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x0 m hb0 hb1 hb3 hb4 h0 h1
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x0_x1 m hb0 hb1 hb3 hb4 h0 h1

end R2N4
