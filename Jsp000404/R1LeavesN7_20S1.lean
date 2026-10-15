import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h564 | h564
  · rcases m.htr 1 2 5 (by decide) (by decide) with h565 | h565
    · rcases m.htr 1 3 4 (by decide) (by decide) with h566 | h566
      · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
        · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
          · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
            · rcases m.htr 2 4 5 (by decide) (by decide) with h570 | h570
              · linarith only [h0, h2, h564, h570, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h2, h564, h567, h570, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h565, h569, h7, hlam]
          · linarith only [h0, h2, h5, h565, h568, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h575 | h575
          · rcases m.htr 2 3 5 (by decide) (by decide) with h576 | h576
            · rcases m.htr 2 4 5 (by decide) (by decide) with h577 | h577
              · linarith only [h0, h564, h567, h577, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h579 | h579
                · linarith only [h564, h567, h575, h579, hlam]
                · rcases h2bigk with h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c | h581c
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h0, h564, h575, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h0, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    rcases p581_3 (m.d 0 2) (by simp) with h585 | h585
                    · rcases p581_3 (m.d 1 2) (by simp) with h586 | h586
                      · linarith only [h0, h586, hlam]
                      · linarith only [h564, h586, hlam]
                    · linarith only [h585, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    rcases p581_3 (m.d 0 2) (by simp) with h590 | h590
                    · rcases p581_3 (m.d 1 2) (by simp) with h591 | h591
                      · linarith only [h0, h591, hlam]
                      · linarith only [h565, h591, hlam]
                    · linarith only [h590, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h0, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h7, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h575, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h0, h2, h575, h577, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h2, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h0, h2, h575, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h0, h2, h575, h577, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h3, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h564, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h575, hlam, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h577, hlam, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h4, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h565, hlam, p581_0]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h576, hlam, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [h565, h575, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p581_1]
                  · have p581_0 := h581c.1
                    have p581_1 := h581c.2.1
                    have p581_2 := h581c.2.2.1
                    have p581_3 := h581c.2.2.2
                    linarith only [hlam, p581_0]
            · linarith only [h565, h576, h7, hlam]
          · linarith only [h0, h2, h5, h565, h575, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h564, h566, h7, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h618 | h618
      · rcases m.htr 1 4 5 (by decide) (by decide) with h619 | h619
        · linarith only [h564, h565, h619, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h621 | h621
          · rcases m.htr 2 3 5 (by decide) (by decide) with h622 | h622
            · rcases m.htr 2 4 5 (by decide) (by decide) with h623 | h623
              · linarith only [h564, h565, h619, h622, h623, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h625 | h625
                · linarith only [h564, h565, h621, h623, h625, hlam]
                · rcases h2bigk with h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h0, h564, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h0, h622, hc01, hc35, hlam, hphi, ht0b, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    rcases p627_3 (m.d 0 2) (by simp) with h631 | h631
                    · rcases p627_3 (m.d 1 2) (by simp) with h632 | h632
                      · linarith only [h0, h632, hlam]
                      · linarith only [h564, h632, hlam]
                    · linarith only [h631, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h0, h564, h565, h621, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h0, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h7, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h621, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h565, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h2, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h0, h2, h621, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h0, h2, h564, h565, h621, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h3, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h564, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h621, hlam, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h623, hlam, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h4, hlam, p627_0]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h564, h621, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h622, hlam, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [h0, h2, h5, h6, h621, h623, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p627_1]
                  · have p627_0 := h627c.1
                    have p627_1 := h627c.2.1
                    have p627_2 := h627c.2.2.1
                    have p627_3 := h627c.2.2.2
                    linarith only [hlam, p627_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h657 | h657
              · linarith only [h564, h622, h657, h7, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h659 | h659
                · linarith only [h0, h2, h5, h564, h622, h657, h659, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h564, h621, h622, h659, h7, hc34, hc45, hlam, hphi]
          · linarith only [h0, h2, h5, h564, h621, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h564, h618, h7, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h664 | h664
    · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
      · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
        · rcases m.htr 2 3 4 (by decide) (by decide) with h667 | h667
          · rcases m.htr 2 3 5 (by decide) (by decide) with h668 | h668
            · rcases m.htr 2 4 5 (by decide) (by decide) with h669 | h669
              · rcases m.htr 3 4 5 (by decide) (by decide) with h670 | h670
                · rcases h2bigk with h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, h664, h668, h670, hc01, hc45, hlam, hphi, ht0b, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, h664, h668, h670, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, h564, h664, h668, h670, hc01, hc45, hlam, hphi, ht0b, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    rcases p671_3 (m.d 0 2) (by simp) with h676 | h676
                    · rcases p671_3 (m.d 1 2) (by simp) with h677 | h677
                      · linarith only [h0, h677, hlam]
                      · linarith only [h664, h677, hlam]
                    · linarith only [h676, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h7, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h564, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h564, h667, h668, h670, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h2, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, h2, h668, h670, hc01, hc45, hlam, hphi, ht0b, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h3, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h664, h668, h670, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h667, hlam, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h0, h2, h667, h668, h670, hc01, hc45, hlam, hphi, ht0b, ht5b, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h4, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h664, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h668, hlam, p671_1]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [h669, hlam, p671_0]
                  · have p671_0 := h671c.1
                    have p671_1 := h671c.2.1
                    have p671_2 := h671c.2.2.1
                    have p671_3 := h671c.2.2.2
                    linarith only [hlam, p671_0]
                · linarith only [h0, h2, h564, h664, h667, h669, h670, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h2, h5, h564, h6, h664, h669, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h564, h664, h667, h668, hlam]
          · linarith only [h0, h2, h5, h664, h667, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h564, h664, h666, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h706 | h706
        · rcases m.htr 2 3 4 (by decide) (by decide) with h707 | h707
          · linarith only [h0, h2, h664, h665, h7, h707, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h2, h5, h664, h7, h707, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h664, h665, h7, h706, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h711 | h711
      · rcases m.htr 1 4 5 (by decide) (by decide) with h712 | h712
        · rcases m.htr 2 3 4 (by decide) (by decide) with h713 | h713
          · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
            · rcases m.htr 2 4 5 (by decide) (by decide) with h715 | h715
              · rcases m.htr 3 4 5 (by decide) (by decide) with h716 | h716
                · rcases h2bigk with h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c | h717c
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    rcases p717_3 (m.d 0 2) (by simp) with h719 | h719
                    · rcases p717_3 (m.d 1 2) (by simp) with h720 | h720
                      · linarith only [h0, h720, hlam]
                      · rcases p717_3 (m.d 2 3) (by simp) with h722 | h722
                        · linarith only [h2, h722, hlam]
                        · linarith only [h7, h722, hlam]
                    · linarith only [h0, h719, hlam]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h0, h7, h711, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h0, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h0, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h0, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h7, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h564, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h664, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h2, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h0, h2, h564, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h0, h2, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h3, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h713, hlam, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h0, h2, h664, h713, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h4, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h714, hlam, p717_1]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [h715, hlam, p717_0]
                  · have p717_0 := h717c.1
                    have p717_1 := h717c.2.1
                    have p717_2 := h717c.2.2.1
                    have p717_3 := h717c.2.2.2
                    linarith only [hlam, p717_0]
                · rcases h2bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    rcases p749_3 (m.d 0 2) (by simp) with h751 | h751
                    · rcases p749_3 (m.d 1 2) (by simp) with h752 | h752
                      · linarith only [h0, h752, hlam]
                      · rcases p749_3 (m.d 2 3) (by simp) with h754 | h754
                        · linarith only [h2, h754, hlam]
                        · linarith only [h7, h754, hlam]
                    · linarith only [h0, h751, hlam]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h0, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h0, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h0, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h0, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h7, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h564, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h664, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h2, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h0, h2, h564, h712, h716, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h0, h2, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h3, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h713, hlam, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h0, h2, h664, h713, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h4, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h714, hlam, p749_1]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [h715, hlam, p749_0]
                  · have p749_0 := h749c.1
                    have p749_1 := h749c.2.1
                    have p749_2 := h749c.2.2.1
                    have p749_3 := h749c.2.2.2
                    linarith only [hlam, p749_0]
              · linarith only [h1, h564, h712, h715, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h782 | h782
              · linarith only [h713, h714, h782, hlam]
              · linarith only [h564, h7, h711, h712, h714, h782, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h7, h711, h713, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h786 | h786
          · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
            · rcases m.htr 2 4 5 (by decide) (by decide) with h788 | h788
              · rcases m.htr 3 4 5 (by decide) (by decide) with h789 | h789
                · linarith only [h711, h712, h789, hlam]
                · rcases h2bigk with h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    rcases p791_3 (m.d 0 2) (by simp) with h793 | h793
                    · rcases p791_3 (m.d 1 2) (by simp) with h794 | h794
                      · linarith only [h0, h794, hlam]
                      · rcases p791_3 (m.d 2 3) (by simp) with h796 | h796
                        · linarith only [h2, h796, hlam]
                        · linarith only [h7, h796, hlam]
                    · linarith only [h0, h793, hlam]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h0, h564, h712, h786, h788, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h0, h564, h712, h788, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h0, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h0, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h7, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h564, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h664, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h2, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h0, h2, h564, h712, h788, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h0, h2, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h3, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h786, hlam, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h0, h2, h664, h786, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h4, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h787, hlam, p791_1]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [h788, hlam, p791_0]
                  · have p791_0 := h791c.1
                    have p791_1 := h791c.2.1
                    have p791_2 := h791c.2.2.1
                    have p791_3 := h791c.2.2.2
                    linarith only [hlam, p791_0]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h823 | h823
                · linarith only [h0, h2, h664, h7, h711, h788, h823, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h2bigk with h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c | h825c
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    rcases p825_3 (m.d 0 2) (by simp) with h827 | h827
                    · rcases p825_3 (m.d 1 2) (by simp) with h828 | h828
                      · linarith only [h0, h828, hlam]
                      · rcases p825_3 (m.d 2 3) (by simp) with h830 | h830
                        · linarith only [h2, h830, hlam]
                        · linarith only [h7, h830, hlam]
                    · linarith only [h0, h827, hlam]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h0, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h0, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h0, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h0, hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h7, hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h564, hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h664, hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h2, hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h0, h2, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h0, h2, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h3, hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h6, h788, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h786, hlam, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h788, hlam, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h4, hlam, p825_0]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h787, hlam, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [h0, h2, h5, h564, h6, h788, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p825_1]
                  · have p825_0 := h825c.1
                    have p825_1 := h825c.2.1
                    have p825_2 := h825c.2.2.1
                    have p825_3 := h825c.2.2.2
                    linarith only [hlam, p825_0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h857 | h857
              · linarith only [h564, h712, h786, h787, h857, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h859 | h859
                · linarith only [h564, h857, h859, hc12, hc34, hlam, hphi, ht23]
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
                        · linarith only [h2, h866, hlam]
                        · linarith only [h7, h866, hlam]
                    · linarith only [h0, h863, hlam]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h0, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h0, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h0, h7, h787, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h0, hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h7, hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h564, hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h664, hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h2, hlam, p861_0]
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
                    linarith only [h0, h2, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h787, hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h3, hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h786, hlam, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h857, hlam, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h4, hlam, p861_0]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h0, h2, h5, h6, h7, h787, h859, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [h0, h2, h5, h564, h6, h787, h859, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p861_1]
                  · have p861_0 := h861c.1
                    have p861_1 := h861c.2.1
                    have p861_2 := h861c.2.2.1
                    have p861_3 := h861c.2.2.2
                    linarith only [hlam, p861_0]
          · linarith only [h7, h711, h786, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h894 | h894
        · rcases m.htr 2 3 4 (by decide) (by decide) with h895 | h895
          · rcases m.htr 2 3 5 (by decide) (by decide) with h896 | h896
            · rcases m.htr 2 4 5 (by decide) (by decide) with h897 | h897
              · rcases m.htr 3 4 5 (by decide) (by decide) with h898 | h898
                · rcases h2bigk with h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c | h899c
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    rcases p899_3 (m.d 0 2) (by simp) with h901 | h901
                    · rcases p899_3 (m.d 1 2) (by simp) with h902 | h902
                      · linarith only [h0, h902, hlam]
                      · rcases p899_3 (m.d 2 3) (by simp) with h904 | h904
                        · linarith only [h2, h904, hlam]
                        · linarith only [h7, h904, hlam]
                    · linarith only [h0, h901, hlam]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h0, h711, h895, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h0, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h0, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h0, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h7, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h564, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h664, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h2, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h0, h2, h564, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h0, h2, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h3, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h895, hlam, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h0, h2, h664, h895, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h4, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h896, hlam, p899_1]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [h897, hlam, p899_0]
                  · have p899_0 := h899c.1
                    have p899_1 := h899c.2.1
                    have p899_2 := h899c.2.2.1
                    have p899_3 := h899c.2.2.2
                    linarith only [hlam, p899_0]
                · linarith only [h1, h7, h711, h894, h898, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h2, h711, h894, h895, h897, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h7, h711, h895, h896, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h934 | h934
            · rcases m.htr 2 4 5 (by decide) (by decide) with h935 | h935
              · rcases m.htr 3 4 5 (by decide) (by decide) with h936 | h936
                · rcases h2bigk with h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c | h937c
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    rcases p937_3 (m.d 0 2) (by simp) with h939 | h939
                    · rcases p937_3 (m.d 1 2) (by simp) with h940 | h940
                      · linarith only [h0, h940, hlam]
                      · rcases p937_3 (m.d 2 3) (by simp) with h942 | h942
                        · linarith only [h2, h942, hlam]
                        · linarith only [h7, h942, hlam]
                    · linarith only [h0, h939, hlam]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, h664, h934, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, h564, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h7, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h564, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h664, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h2, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h895, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h664, hc12, hc23, hlam, hphi, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h3, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, h2, h5, h895, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h0, h2, h5, h664, h895, hc01, hc15, hlam, hphi, ht0b, ht5b, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h4, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h934, hlam, p937_1]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [h935, hlam, p937_0]
                  · have p937_0 := h937c.1
                    have p937_1 := h937c.2.1
                    have p937_2 := h937c.2.2.1
                    have p937_3 := h937c.2.2.2
                    linarith only [hlam, p937_0]
                · linarith only [h0, h2, h5, h6, h7, h895, h936, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h564, h664, h894, h895, h934, h935, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h971 | h971
              · rcases m.htr 3 4 5 (by decide) (by decide) with h972 | h972
                · rcases h2bigk with h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    rcases p973_3 (m.d 0 2) (by simp) with h975 | h975
                    · rcases p973_3 (m.d 1 2) (by simp) with h976 | h976
                      · linarith only [h0, h976, hlam]
                      · rcases p973_3 (m.d 2 3) (by simp) with h978 | h978
                        · linarith only [h2, h978, hlam]
                        · linarith only [h7, h978, hlam]
                    · linarith only [h0, h975, hlam]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, h7, h934, h971, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, h7, h934, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h7, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h564, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h664, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h2, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h895, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h934, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h3, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, h2, h5, h895, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, h2, h5, h895, hc01, hc25, hlam, hphi, ht0b, ht5b, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h4, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h0, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p973_1]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [h971, hlam, p973_0]
                  · have p973_0 := h973c.1
                    have p973_1 := h973c.2.1
                    have p973_2 := h973c.2.2.1
                    have p973_3 := h973c.2.2.2
                    linarith only [hlam, p973_0]
                · linarith only [h564, h894, h895, h972, hlam]
              · linarith only [h564, h894, h971, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1007 | h1007
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1008 | h1008
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1009 | h1009
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                · linarith only [h0, h1007, h1010, h2, h894, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1009, h1010, h7, h711, hc12, hc24, hlam, hphi]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1013 | h1013
                · linarith only [h0, h1007, h1009, h1013, h2, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h2bigk with h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    rcases p1015_3 (m.d 0 2) (by simp) with h1017 | h1017
                    · rcases p1015_3 (m.d 1 2) (by simp) with h1018 | h1018
                      · linarith only [h0, h1018, hlam]
                      · rcases p1015_3 (m.d 2 3) (by simp) with h1020 | h1020
                        · linarith only [h1020, h2, hlam]
                        · linarith only [h1020, h7, hlam]
                    · linarith only [h0, h1017, hlam]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h0, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h0, h1007, h7, h711, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h0, h1007, h1009, h7, h711, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h0, hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h7, hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h564, hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h664, hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h2, hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h0, h1007, h2, h7, h711, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h0, h1007, h1009, h2, h7, h711, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h3, hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h1009, h6, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h1007, hlam, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h1009, hlam, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h4, hlam, p1015_0]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h1008, hlam, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [h0, h1009, h2, h5, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1015_1]
                  · have p1015_0 := h1015c.1
                    have p1015_1 := h1015c.2.1
                    have p1015_2 := h1015c.2.2.1
                    have p1015_3 := h1015c.2.2.2
                    linarith only [hlam, p1015_0]
            · linarith only [h1007, h1008, h7, h711, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1048 | h1048
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1049 | h1049
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1050 | h1050
                · linarith only [h0, h1007, h1048, h1050, h2, h5, h7, h711, h894, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1007, h1048, h1049, h1050, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h1007, h1048, h1049, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1054 | h1054
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1055 | h1055
                · rcases h2bigk with h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c | h1056c
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    rcases p1056_3 (m.d 0 2) (by simp) with h1058 | h1058
                    · rcases p1056_3 (m.d 1 2) (by simp) with h1059 | h1059
                      · linarith only [h0, h1059, hlam]
                      · rcases p1056_3 (m.d 2 3) (by simp) with h1061 | h1061
                        · linarith only [h1061, h2, hlam]
                        · linarith only [h1061, h7, hlam]
                    · linarith only [h0, h1058, hlam]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h1054, h711, h894, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h664, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
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
                    linarith only [h7, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h564, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h664, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h2, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1007, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1048, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h3, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h1007, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h1007, h1048, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h4, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h0, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1056_1]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [h1054, hlam, p1056_0]
                  · have p1056_0 := h1056c.1
                    have p1056_1 := h1056c.2.1
                    have p1056_2 := h1056c.2.2.1
                    have p1056_3 := h1056c.2.2.2
                    linarith only [hlam, p1056_0]
                · linarith only [h0, h1007, h1055, h2, h5, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1089 | h1089
                · linarith only [h1054, h1089, h564, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1007, h1089, h2, h5, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6 h7
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h5 h6 h7

end R2N4
