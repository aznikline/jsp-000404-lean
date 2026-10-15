import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h544 | h544
  · rcases m.htr 0 3 5 (by decide) (by decide) with h545 | h545
    · linarith only [h4, h545, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h547 | h547
      · linarith only [h4, h544, h547, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
        · rcases m.htr 1 4 5 (by decide) (by decide) with h550 | h550
          · linarith only [h2, h547, h550, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases h0bigk with h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h0, h549, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h544, hc01, hlam, hphi, ht0b, ht45, ht5b, p552_1, u4ehi3]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p552_1, u4ehi1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p552_1, u4ehi2]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h0, hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h1, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p552_1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h2, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p552_1, u4ehi1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h6, hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h1, hlam, p552_1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h4, hlam, p552_1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h2, hc03, hlam, hphi, ht0b, ht45, ht5b, p552_1, u4ehi1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h545, hlam, p552_1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h2, hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h5, hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h544, hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h547, hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h3, hlam, p552_0]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h0, h549, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p552_1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h544, h545, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p552_1, u4ehi3]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [h2, h547, hc45, hlam, hphi, p552_1, u4ehi1]
            · have p552_0 := h552c.1
              have p552_1 := h552c.2.1
              have p552_2 := h552c.2.2.1
              have p552_3 := h552c.2.2.2
              linarith only [hlam, p552_0]
        · linarith only [h4, h549, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h579 | h579
    · linarith only [h4, h579, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h581 | h581
      · linarith only [h5, h581, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h583 | h583
        · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
          · linarith only [h2, h581, h584, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
          · rcases h0bigk with h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c | h586c
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h0, h583, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              rcases p586_3 (m.d 0 1) (by simp) with h589 | h589
              · rcases p586_3 (m.d 0 2) (by simp) with h590 | h590
                · linarith only [h0, h590, hlam]
                · linarith only [h4, h590, hlam]
              · linarith only [h1, h589, hlam]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p586_1, u4ehi1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p586_1, u4ehi2]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h0, hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h579, h6, hc03, hc35, hlam, hphi, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h2, h581, h6, hc45, hlam, hphi, p586_1, u4ehi1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h6, hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h1, hlam, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h4, hlam, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h544, hlam, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h579, hlam, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h2, hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h5, hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h1, h5, h583, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h581, hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h3, hlam, p586_0]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h581, hc02, hc45, hlam, hphi, ht23, ht34, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h1, h581, h583, hc23, hc45, hlam, hphi, ht34, p586_1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [h2, h581, hc45, hlam, hphi, p586_1, u4ehi1]
            · have p586_0 := h586c.1
              have p586_1 := h586c.2.1
              have p586_2 := h586c.2.2.1
              have p586_3 := h586c.2.2.2
              linarith only [hlam, p586_0]
        · linarith only [h4, h583, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x0_x0 m hb0 hb4 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x0_x1 m hb0 hb4 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h617 | h617
  · rcases m.htr 0 3 4 (by decide) (by decide) with h618 | h618
    · linarith only [h4, h5, h618, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h620 | h620
      · rcases m.htr 0 4 5 (by decide) (by decide) with h621 | h621
        · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
          · rcases m.htr 1 4 5 (by decide) (by decide) with h623 | h623
            · rcases h0bigk with h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c | h624c
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h617, hc01, hc25, hlam, hphi, ht0b, ht5b, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h620, hc01, hc35, hlam, hphi, ht0b, ht5b, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h2, h623, hc01, hlam, hphi, ht0b, ht45, ht5b, p624_1, u4ehi4]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h621, hc01, hlam, hphi, ht0b, ht45, ht5b, p624_1, u4ehi4]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h0, hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h620, hc02, hc35, hlam, hphi, ht0b, ht5b, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h5, hlam, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h3, h5, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h1, hlam, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h4, hlam, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h618, hlam, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h3, h4, h5, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h2, hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h618, hc02, hc34, hlam, hphi, ht23, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h618, hc03, hc34, hlam, hphi, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h618, h621, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p624_1, u4ehi4]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h3, hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h617, hlam, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h620, hlam, p624_0]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [h621, hlam, p624_1]
              · have p624_0 := h624c.1
                have p624_1 := h624c.2.1
                have p624_2 := h624c.2.2.1
                have p624_3 := h624c.2.2.2
                linarith only [hlam, p624_0]
            · rcases h0bigk with h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c | h650c
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h0, h622, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h620, h621, h623, hc01, hlam, hphi, ht0b, ht45, ht5b, p650_1, u4ehi1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p650_1, u4ehi0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h621, h623, hc01, hlam, hphi, ht0b, ht45, ht5b, p650_1, u4ehi1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h0, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h620, h621, h623, hc02, hlam, hphi, ht0b, ht45, ht5b, p650_1, u4ehi1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h5, hlam, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h5, h621, h623, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p650_1, u4ehi1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h1, hlam, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h4, hlam, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h618, hlam, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h621, h623, hc03, hlam, hphi, ht0b, ht45, ht5b, p650_1, u4ehi1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h2, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h0, h622, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h618, hc03, hc34, hlam, hphi, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h618, h621, h623, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p650_1, u4ehi1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h3, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h617, hlam, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h620, hlam, p650_0]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [h621, hlam, p650_1]
              · have p650_0 := h650c.1
                have p650_1 := h650c.2.1
                have p650_2 := h650c.2.2.1
                have p650_3 := h650c.2.2.2
                linarith only [hlam, p650_0]
          · linarith only [h4, h5, h622, hc12, hc24, hlam, hphi]
        · linarith only [h5, h617, h621, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h678 | h678
        · rcases m.htr 1 2 3 (by decide) (by decide) with h679 | h679
          · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
            · rcases h0bigk with h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c | h681c
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [hlam, p681_0]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h0, h679, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                rcases p681_3 (m.d 0 1) (by simp) with h684 | h684
                · rcases p681_3 (m.d 0 2) (by simp) with h685 | h685
                  · linarith only [h0, h685, hlam]
                  · linarith only [h4, h685, hlam]
                · linarith only [h1, h684, hlam]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h2, h680, hc01, hlam, hphi, ht0b, ht45, ht5b, p681_1, u4ehi4]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h3, h680, hc01, hlam, hphi, ht0b, ht45, ht5b, p681_1, u4ehi4]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h0, hlam, p681_0]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [hlam, p681_0]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h1, h5, h679, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h5, hlam, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h3, h5, h680, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p681_1, u4ehi4]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h1, hlam, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h4, hlam, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [hlam, p681_0]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h618, hlam, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h620, hlam, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h2, hlam, p681_0]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h0, h679, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h1, h618, h679, hc23, hc34, hlam, hphi, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [hlam, p681_0]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h3, h618, h680, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p681_1, u4ehi4]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h3, hlam, p681_0]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h617, hlam, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h1, h5, h617, h679, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [h678, hlam, p681_1]
              · have p681_0 := h681c.1
                have p681_1 := h681c.2.1
                have p681_2 := h681c.2.2.1
                have p681_3 := h681c.2.2.2
                linarith only [hlam, p681_0]
            · rcases h0bigk with h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [hlam, p711_0]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h0, h618, h678, h679, h680, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p711_1, u4ehi1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                rcases p711_3 (m.d 0 1) (by simp) with h714 | h714
                · rcases p711_3 (m.d 0 2) (by simp) with h715 | h715
                  · linarith only [h0, h715, hlam]
                  · linarith only [h4, h715, hlam]
                · linarith only [h1, h714, hlam]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h678, h680, hc01, hlam, hphi, ht0b, ht45, ht5b, p711_1, u4ehi1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h678, h680, hc01, hlam, hphi, ht0b, ht45, ht5b, p711_1, u4ehi1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h0, hlam, p711_0]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [hlam, p711_0]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h1, h5, h618, h678, h679, h680, hc23, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p711_1, u4ehi1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h5, hlam, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h5, h678, h680, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p711_1, u4ehi1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h1, hlam, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h4, hlam, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [hlam, p711_0]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h618, hlam, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h620, hlam, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h2, hlam, p711_0]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h618, hc02, hc34, hlam, hphi, ht23, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h1, h618, h679, hc23, hc34, hlam, hphi, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [hlam, p711_0]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h618, h678, h680, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p711_1, u4ehi1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h3, hlam, p711_0]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h617, hlam, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h1, h620, h679, hc23, hc35, hlam, hphi, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [h678, hlam, p711_1]
              · have p711_0 := h711c.1
                have p711_1 := h711c.2.1
                have p711_2 := h711c.2.2.1
                have p711_3 := h711c.2.2.2
                linarith only [hlam, p711_0]
          · linarith only [h4, h5, h679, hc12, hc24, hlam, hphi]
        · linarith only [h5, h617, h678, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h743 | h743
    · linarith only [h4, h5, h743, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h745 | h745
      · linarith only [h4, h617, h745, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h747 | h747
        · rcases m.htr 1 2 3 (by decide) (by decide) with h748 | h748
          · rcases m.htr 1 4 5 (by decide) (by decide) with h749 | h749
            · rcases h0bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h0, h748, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                rcases p750_3 (m.d 0 1) (by simp) with h753 | h753
                · rcases p750_3 (m.d 0 2) (by simp) with h754 | h754
                  · linarith only [h0, h754, hlam]
                  · linarith only [h4, h754, hlam]
                · linarith only [h1, h753, hlam]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p750_1, u4ehi0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h3, h749, hc01, hlam, hphi, ht0b, ht45, ht5b, p750_1, u4ehi4]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h0, hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h5, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h5, hlam, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h617, hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h1, hlam, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h4, hlam, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h743, hlam, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h745, hlam, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h2, hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h743, hc02, hc34, hlam, hphi, ht23, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h1, h743, h748, hc23, hc34, hlam, hphi, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h0, h617, h743, h748, hc23, hc34, hlam, hphi, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h3, hlam, p750_0]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h0, h748, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h1, h745, h748, hc23, hc35, hlam, hphi, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [h747, hlam, p750_1]
              · have p750_0 := h750c.1
                have p750_1 := h750c.2.1
                have p750_2 := h750c.2.2.1
                have p750_3 := h750c.2.2.2
                linarith only [hlam, p750_0]
            · rcases h0bigk with h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c | h780c
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h0, h743, h747, h748, h749, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p780_1, u4ehi1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                rcases p780_3 (m.d 0 1) (by simp) with h783 | h783
                · rcases p780_3 (m.d 0 2) (by simp) with h784 | h784
                  · linarith only [h0, h784, hlam]
                  · linarith only [h4, h784, hlam]
                · linarith only [h1, h783, hlam]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h747, h749, hc01, hlam, hphi, ht0b, ht45, ht5b, p780_1, u4ehi1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h0, h617, h743, h747, h748, h749, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p780_1, u4ehi1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h0, hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h1, h617, h743, h747, h748, h749, hc23, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p780_1, u4ehi1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h5, hlam, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h617, hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h1, hlam, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h4, hlam, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h743, hlam, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h745, hlam, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h2, hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h743, hc02, hc34, hlam, hphi, ht23, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h1, h743, h748, hc23, hc34, hlam, hphi, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h0, h617, h743, h748, hc23, hc34, hlam, hphi, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h3, hlam, p780_0]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h0, h743, h747, h748, h749, hc05, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p780_1, u4ehi1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h1, h745, h748, hc23, hc35, hlam, hphi, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [h747, hlam, p780_1]
              · have p780_0 := h780c.1
                have p780_1 := h780c.2.1
                have p780_2 := h780c.2.2.1
                have p780_3 := h780c.2.2.2
                linarith only [hlam, p780_0]
          · linarith only [h4, h5, h748, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h811 | h811
          · rcases m.htr 1 4 5 (by decide) (by decide) with h812 | h812
            · linarith only [h2, h747, h812, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases h0bigk with h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h0, h811, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                rcases p814_3 (m.d 0 1) (by simp) with h817 | h817
                · rcases p814_3 (m.d 0 2) (by simp) with h818 | h818
                  · linarith only [h0, h818, hlam]
                  · linarith only [h4, h818, hlam]
                · linarith only [h1, h817, hlam]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h0, h5, h811, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h0, h617, h811, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h0, hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h1, h5, h743, h811, hc23, hc34, hlam, hphi, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h5, hlam, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h617, hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h1, hlam, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h4, hlam, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h743, hlam, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h745, hlam, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h2, hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h743, hc02, hc34, hlam, hphi, ht23, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h1, h743, h811, hc23, hc34, hlam, hphi, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h747, hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h3, hlam, p814_0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h0, h811, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h1, h745, h811, hc23, hc35, hlam, hphi, p814_1]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [h747, hc45, hlam, hphi, p814_1, u4ehi0]
              · have p814_0 := h814c.1
                have p814_1 := h814c.2.1
                have p814_2 := h814c.2.2.1
                have p814_3 := h814c.2.2.2
                linarith only [hlam, p814_0]
          · linarith only [h4, h5, h811, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x0 m hb0 hb4 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_14_H_I_L_R_x0_x0_x0_x0_x0_x1 m hb0 hb4 h0 h1 h2 h3 h4 h5

end R2N4
