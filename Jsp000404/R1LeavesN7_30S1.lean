import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h612 | h612
  · rcases m.htr 0 3 4 (by decide) (by decide) with h613 | h613
    · linarith only [h4, h5, h613, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h615 | h615
      · rcases m.htr 0 4 5 (by decide) (by decide) with h616 | h616
        · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
          · rcases m.htr 2 3 4 (by decide) (by decide) with h618 | h618
            · linarith only [h0, h5, h613, h617, h618, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases h0bigk with h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h0, h617, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h615, hc01, hlam, hphi, ht0b, ht5b, p620_1, u5ehi3]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h0, h5, h617, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p620_1, u5ehi1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h0, hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h615, hc02, hlam, hphi, ht0b, ht5b, p620_1, u5ehi3]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h5, hlam, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h3, h5, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p620_1, u5ehi1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h1, hlam, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h4, hlam, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h613, hlam, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h3, h4, h5, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p620_1, u5ehi1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h2, hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h5, h618, hc02, hc34, hlam, hphi, ht23, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h1, h5, h618, hc13, hc34, hlam, hphi, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h3, h5, h618, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p620_1, u5ehi1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h3, hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h612, hlam, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h615, hlam, p620_0]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [h616, hlam, p620_1]
              · have p620_0 := h620c.1
                have p620_1 := h620c.2.1
                have p620_2 := h620c.2.2.1
                have p620_3 := h620c.2.2.2
                linarith only [hlam, p620_0]
          · linarith only [h4, h5, h617, hc12, hc24, hlam, hphi]
        · linarith only [h5, h612, h616, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h648 | h648
        · rcases m.htr 1 2 3 (by decide) (by decide) with h649 | h649
          · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
            · linarith only [h0, h613, h649, h650, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases h0bigk with h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c | h652c
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [hlam, p652_0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h612, hc01, hlam, hphi, ht0b, ht5b, p652_1, u5ehi0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                rcases p652_3 (m.d 0 1) (by simp) with h655 | h655
                · rcases p652_3 (m.d 0 2) (by simp) with h656 | h656
                  · linarith only [h0, h656, hlam]
                  · linarith only [h4, h656, hlam]
                · linarith only [h1, h655, hlam]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h5, h612, hc01, hlam, hphi, ht0b, ht5b, p652_1, u5ehi2]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p652_1, u5ehi1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h0, hlam, p652_0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [hlam, p652_0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h1, h5, h649, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h5, hlam, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h3, h5, h650, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p652_1, u5ehi1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h1, hlam, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h4, hlam, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [hlam, p652_0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h613, hlam, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h615, hlam, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h2, hlam, p652_0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h2, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h1, h5, h649, h650, hc23, hc34, hlam, hphi, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [hlam, p652_0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h3, h5, h650, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p652_1, u5ehi1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h3, hlam, p652_0]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h612, hlam, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h1, h5, h612, h649, h650, hc23, hc34, hlam, hphi, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [h648, hlam, p652_1]
              · have p652_0 := h652c.1
                have p652_1 := h652c.2.1
                have p652_2 := h652c.2.2.1
                have p652_3 := h652c.2.2.2
                linarith only [hlam, p652_0]
          · linarith only [h4, h5, h649, hc12, hc24, hlam, hphi]
        · linarith only [h5, h612, h648, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h684 | h684
    · linarith only [h4, h5, h684, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h686 | h686
      · linarith only [h4, h612, h686, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h688 | h688
        · rcases m.htr 1 2 3 (by decide) (by decide) with h689 | h689
          · rcases m.htr 2 3 4 (by decide) (by decide) with h690 | h690
            · linarith only [h0, h5, h684, h689, h690, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
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
                linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                rcases p692_3 (m.d 0 1) (by simp) with h695 | h695
                · rcases p692_3 (m.d 0 2) (by simp) with h696 | h696
                  · linarith only [h0, h696, hlam]
                  · linarith only [h4, h696, hlam]
                · linarith only [h1, h695, hlam]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h688, hc01, hlam, hphi, ht0b, ht5b, p692_1, u5ehi4]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h0, h612, h689, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1]
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
                linarith only [h1, h5, h689, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h5, hlam, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h612, hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h1, hlam, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h4, hlam, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h684, hlam, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h686, hlam, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h2, hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h0, h689, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h1, h5, h689, h690, hc23, hc34, hlam, hphi, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h0, h5, h612, h689, h690, hc23, hc34, hlam, hphi, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h3, hlam, p692_0]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h0, h689, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h1, h686, h689, hc23, hc35, hlam, hphi, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [h688, hlam, p692_1]
              · have p692_0 := h692c.1
                have p692_1 := h692c.2.1
                have p692_2 := h692c.2.2.1
                have p692_3 := h692c.2.2.2
                linarith only [hlam, p692_0]
          · linarith only [h4, h5, h689, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
          · rcases m.htr 2 3 4 (by decide) (by decide) with h724 | h724
            · linarith only [h0, h5, h688, h723, h724, hc34, hc45, hlam, hphi]
            · rcases h0bigk with h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c | h726c
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h0, h723, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                rcases p726_3 (m.d 0 1) (by simp) with h729 | h729
                · rcases p726_3 (m.d 0 2) (by simp) with h730 | h730
                  · linarith only [h0, h730, hlam]
                  · linarith only [h4, h730, hlam]
                · linarith only [h1, h729, hlam]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h0, h5, h723, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p726_1, u5ehi0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h0, hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h1, h5, h723, h724, hc23, hc34, hlam, hphi, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h5, hlam, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h612, hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h1, hlam, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h4, hlam, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h684, hlam, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h686, hlam, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h2, hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h0, h723, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h1, h5, h723, h724, hc23, hc34, hlam, hphi, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h688, hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h3, hlam, p726_0]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h0, h723, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h1, h686, h723, hc23, hc35, hlam, hphi, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [h688, hc04, hc45, hlam, hphi, p726_1]
              · have p726_0 := h726c.1
                have p726_1 := h726c.2.1
                have p726_2 := h726c.2.2.1
                have p726_3 := h726c.2.2.2
                linarith only [hlam, p726_0]
          · linarith only [h4, h5, h723, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5

end R2N4
