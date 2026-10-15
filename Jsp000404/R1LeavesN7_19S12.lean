import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h7104 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7105 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  have h5235 := hg5235
  rcases m.htr 0 4 5 (by decide) (by decide) with h7655 | h7655
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7656 | h7656
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7657 | h7657
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7658 | h7658
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7659 | h7659
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7660 | h7660
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7661 | h7661
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7662 | h7662
                · linarith only [h5235, h7105, h7656, h7662, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7664 | h7664
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7665 | h7665
                    · rcases h1bigk with h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c | h7666c
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h0, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h5235, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h6110, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h6504, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h5235, h7105, h7659, hc01, hc12, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h7656, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h6110, h7104, h7656, h7664, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h6504, h7656, hc01, hc12, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h7657, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h7659, hlam, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h6504, h7656, h7659, hc01, hc12, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7666_1]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h7658, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h7660, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [h7661, hlam, p7666_0]
                      · have p7666_0 := h7666c.1
                        have p7666_1 := h7666c.2.1
                        have p7666_2 := h7666c.2.2.1
                        have p7666_3 := h7666c.2.2.2
                        linarith only [hlam, p7666_0]
                    · linarith only [h5235, h7105, h7664, h7665, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7693 | h7693
                    · rcases h1bigk with h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c | h7694c
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h0, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h5235, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h6110, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h6504, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h7105, h7655, h7659, h7662, h7664, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h7656, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h6110, h7655, h7656, h7662, h7664, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h6504, h7656, hc01, hc12, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h7657, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h7659, hlam, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h6504, h7656, h7659, hc01, hc12, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7694_1]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h7658, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h7660, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [h7661, hlam, p7694_0]
                      · have p7694_0 := h7694c.1
                        have p7694_1 := h7694c.2.1
                        have p7694_2 := h7694c.2.2.1
                        have p7694_3 := h7694c.2.2.2
                        linarith only [hlam, p7694_0]
                    · linarith only [h7105, h7655, h7693, hlam]
              · linarith only [h6110, h7105, h7655, h7661, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h5235, h7105, h7659, h7660, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7723 | h7723
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7724 | h7724
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7725 | h7725
                · linarith only [h6504, h7659, h7723, h7725, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7727 | h7727
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7728 | h7728
                    · rcases h1bigk with h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c | h7729c
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h0, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h5235, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h6110, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h6504, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h6504, h7723, hc01, hc12, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7656, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7659, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h6504, hc01, hc13, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7657, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7723, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h6504, h7659, hc01, hc34, hlam, hphi, ht12, ht23, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7723, hc01, hc13, hlam, hphi, p7729_1]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7658, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7723, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [h7724, hlam, p7729_0]
                      · have p7729_0 := h7729c.1
                        have p7729_1 := h7729c.2.1
                        have p7729_2 := h7729c.2.2.1
                        have p7729_3 := h7729c.2.2.2
                        linarith only [hlam, p7729_0]
                    · linarith only [h5235, h7659, h7727, h7728, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7756 | h7756
                    · linarith only [h7659, h7723, h7725, h7727, h7756, hc23, hc34, hlam, hphi]
                    · linarith only [h5235, h6504, h7655, h7659, h7756, hc01, hc15, hlam, hphi]
              · linarith only [h6110, h6504, h7655, h7659, h7723, h7724, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7760 | h7760
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7761 | h7761
                · linarith only [h5235, h7105, h7656, h7723, h7761, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7763 | h7763
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7764 | h7764
                    · rcases h1bigk with h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c | h7765c
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h0, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h5235, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h6110, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h6504, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h7656, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h7659, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h7723, hlam, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h7657, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h7659, hc13, hc34, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h5235, h7659, h7723, hc01, hc34, hlam, hphi, ht12, ht23, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h7658, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h5235, h7723, h7764, hc01, hc34, hlam, hphi, ht12, ht23, p7765_1]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [h7760, hlam, p7765_0]
                      · have p7765_0 := h7765c.1
                        have p7765_1 := h7765c.2.1
                        have p7765_2 := h7765c.2.2.1
                        have p7765_3 := h7765c.2.2.2
                        linarith only [hlam, p7765_0]
                    · linarith only [h0, h6110, h7104, h7659, h7763, h7764, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7792 | h7792
                    · rcases h1bigk with h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c | h7793c
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h0, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h5235, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h6110, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h6504, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h7656, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h7659, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h7723, hlam, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h7657, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h7659, hc13, hc34, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h5235, h7659, h7723, hc01, hc34, hlam, hphi, ht12, ht23, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h7658, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h5235, h7723, hc01, hc35, hlam, hphi, ht12, ht23, p7793_1]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [h7760, hlam, p7793_0]
                      · have p7793_0 := h7793c.1
                        have p7793_1 := h7793c.2.1
                        have p7793_2 := h7793c.2.2.1
                        have p7793_3 := h7793c.2.2.2
                        linarith only [hlam, p7793_0]
                    · linarith only [h6110, h7655, h7659, h7792, hlam]
              · linarith only [h6110, h7655, h7760, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7821 | h7821
          · linarith only [h5235, h7105, h7656, h7658, h7821, hc01, hc25, hlam, hphi, ht12]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7823 | h7823
            · linarith only [h7656, h7658, h7823, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7825 | h7825
              · linarith only [h7657, h7658, h7825, hlam]
              · linarith only [h0, h5235, h7104, h7655, h7821, h7825, hc01, hc12, hlam, hphi]
      · linarith only [h0, h7104, h7657, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7829 | h7829
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7830 | h7830
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7831 | h7831
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7832 | h7832
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7833 | h7833
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7834 | h7834
                · linarith only [h7104, h7105, h7834, hlam]
                · linarith only [h7656, h7830, h7831, h7834, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h6110, h7655, h7833, hlam]
            · linarith only [h5235, h7105, h7831, h7832, hc01, hc35, hlam, hphi, ht12, ht23]
          · linarith only [h7656, h7829, h7831, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7840 | h7840
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7841 | h7841
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7842 | h7842
              · linarith only [h7829, h7830, h7842, hlam]
              · linarith only [h6110, h7105, h7655, h7840, h7842, hc01, hc13, hlam, hphi]
            · linarith only [h5235, h7105, h7840, h7841, hc01, hc35, hlam, hphi, ht12, ht23]
          · linarith only [h7656, h7829, h7840, hlam]
      · linarith only [h0, h7104, h7829, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7848 | h7848
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7849 | h7849
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7850 | h7850
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7851 | h7851
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7852 | h7852
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7853 | h7853
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7854 | h7854
                · linarith only [h5235, h7105, h7848, h7854, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7856 | h7856
                  · linarith only [h7104, h7655, h7856, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7858 | h7858
                    · linarith only [h6110, h7655, h7848, h7851, h7858, hc01, hc12, hlam, hphi]
                    · linarith only [h5235, h7105, h7848, h7851, h7853, h7858, hc01, hc12, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7861 | h7861
                · linarith only [h5235, h7105, h7848, h7861, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7863 | h7863
                  · linarith only [h5235, h7105, h7851, h7853, h7863, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7865 | h7865
                    · linarith only [h7851, h7853, h7865, hlam]
                    · rcases h1bigk with h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c | h7867c
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h0, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h5235, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h6110, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h6504, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7852, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h5235, h7105, h7851, hc01, hc12, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7848, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h5235, h7105, h7848, h7851, hc01, hc12, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h6110, h6504, h7655, h7848, hc01, hc12, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7849, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7851, hlam, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7853, hlam, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7850, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7852, hlam, p7867_0]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [h7853, hc14, hc45, hlam, hphi, p7867_1]
                      · have p7867_0 := h7867c.1
                        have p7867_1 := h7867c.2.1
                        have p7867_2 := h7867c.2.2.1
                        have p7867_3 := h7867c.2.2.2
                        linarith only [hlam, p7867_0]
            · linarith only [h5235, h7105, h7851, h7852, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7894 | h7894
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7895 | h7895
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7896 | h7896
                · linarith only [h5235, h7851, h7896, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7898 | h7898
                  · linarith only [h7104, h7655, h7898, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7900 | h7900
                    · linarith only [h5235, h7105, h7655, h7851, h7894, h7900, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h7851, h7894, h7895, h7900, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h7851, h7894, h7895, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7904 | h7904
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7905 | h7905
                · linarith only [h7105, h7655, h7848, h7851, h7894, h7904, h7905, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7907 | h7907
                  · linarith only [h7104, h7655, h7907, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7909 | h7909
                    · rcases h1bigk with h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c | h7910c
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h0, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h5235, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h6110, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h6504, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h5235, h7105, h7655, h7904, hc01, hc12, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h5235, h7894, hc01, hc12, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h7848, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h7851, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h7894, hlam, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h7849, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h7851, hc13, hc34, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h6504, h7851, hc01, hc34, hlam, hphi, ht12, ht23, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h7850, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h5235, h7894, h7909, hc01, hc34, hlam, hphi, ht12, ht23, p7910_1]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [h7904, hlam, p7910_0]
                      · have p7910_0 := h7910c.1
                        have p7910_1 := h7910c.2.1
                        have p7910_2 := h7910c.2.2.1
                        have p7910_3 := h7910c.2.2.2
                        linarith only [hlam, p7910_0]
                    · linarith only [h5235, h7851, h7909, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7937 | h7937
                · linarith only [h5235, h7851, h7937, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7939 | h7939
                  · linarith only [h7104, h7655, h7939, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7941 | h7941
                    · linarith only [h6110, h7904, h7941, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h5235, h7851, h7941, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7944 | h7944
          · linarith only [h5235, h7105, h7848, h7850, h7944, hc01, hc25, hlam, hphi, ht12]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7946 | h7946
            · linarith only [h7849, h7850, h7944, h7946, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7948 | h7948
              · linarith only [h5235, h7105, h7655, h7849, h7850, h7948, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7950 | h7950
                · linarith only [h7848, h7850, h7944, h7950, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7952 | h7952
                  · linarith only [h6110, h7948, h7952, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7954 | h7954
                    · linarith only [h0, h7850, h7952, h7954, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h5235, h7944, h7954, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h7104, h7849, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7958 | h7958
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7959 | h7959
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7960 | h7960
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7961 | h7961
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7962 | h7962
              · linarith only [h5235, h7105, h7655, h7848, h7958, h7962, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7964 | h7964
                · linarith only [h0, h5235, h7104, h7105, h7848, h7964, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h7848, h7959, h7960, h7964, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h5235, h7105, h7960, h7961, hc01, hc35, hlam, hphi, ht12, ht23]
          · linarith only [h7848, h7958, h7960, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7969 | h7969
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7970 | h7970
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7971 | h7971
              · linarith only [h5235, h7105, h7655, h7958, h7959, h7971, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7973 | h7973
                · linarith only [h0, h5235, h7104, h7105, h7959, h7973, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h7104, h7848, h7969, h7973, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h7105, h7969, h7970, hc03, hc35, hlam, hphi]
          · linarith only [h7848, h7958, h7969, hlam]
      · linarith only [h0, h7104, h7958, hlam]

set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h7104 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  have h5235 := hg5235
  rcases m.htr 0 3 4 (by decide) (by decide) with h7105 | h7105
  · exact r1l7_21_14_H_I_L_I_s6_x1_x1_x0_x0 m hb1 hb4 hg0 hg5235 h6110 h6504 h7104 h7105
  · exact r1l7_21_14_H_I_L_I_s6_x1_x1_x0_x1 m hb1 hb4 hg0 hg5235 h6110 h6504 h7104 h7105

set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h7104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7979 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h5235 := hg5235
  rcases m.htr 0 4 5 (by decide) (by decide) with h7980 | h7980
  · rcases m.htr 1 2 3 (by decide) (by decide) with h7981 | h7981
    · rcases m.htr 1 2 4 (by decide) (by decide) with h7982 | h7982
      · rcases m.htr 1 2 5 (by decide) (by decide) with h7983 | h7983
        · rcases m.htr 1 3 4 (by decide) (by decide) with h7984 | h7984
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7985 | h7985
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7986 | h7986
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7987 | h7987
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7988 | h7988
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7989 | h7989
                    · rcases h1bigk with h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c | h7990c
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h0, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h5235, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h6110, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h6504, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h7104, h7982, h7984, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h0, h7104, h7982, hc01, hc12, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h7981, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h0, h7104, h7981, h7982, hc01, hc12, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h6504, h7981, hc01, hc12, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h7982, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h7984, hlam, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h6504, h7981, h7984, hc01, hc12, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p7990_1]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h7983, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h7985, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [h7986, hlam, p7990_0]
                      · have p7990_0 := h7990c.1
                        have p7990_1 := h7990c.2.1
                        have p7990_2 := h7990c.2.2.1
                        have p7990_3 := h7990c.2.2.2
                        linarith only [hlam, p7990_0]
                    · rcases h1bigk with h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c | h8016c
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h0, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h5235, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h6110, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h6504, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h7981, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h7104, h7980, h7981, h7982, h7989, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h6504, h7981, hc01, hc12, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h7982, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h7984, hlam, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h6504, h7981, h7984, hc01, hc12, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8016_1]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h7983, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h7985, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [h7986, hlam, p8016_0]
                      · have p8016_0 := h8016c.1
                        have p8016_1 := h8016c.2.1
                        have p8016_2 := h8016c.2.2.1
                        have p8016_3 := h8016c.2.2.2
                        linarith only [hlam, p8016_0]
                  · linarith only [h7104, h7980, h7988, hlam]
                · linarith only [h7104, h7979, h7987, hlam]
              · linarith only [h6110, h7104, h7980, h7986, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8045 | h8045
              · linarith only [h7984, h7985, h8045, hlam]
              · linarith only [h7104, h7980, h7982, h8045, hlam]
          · linarith only [h5235, h7979, h7984, hlam]
        · linarith only [h0, h7104, h7982, h7983, hc01, hc25, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8050 | h8050
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8051 | h8051
          · linarith only [h7981, h7982, h8051, hlam]
          · linarith only [h5235, h7979, h8051, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8054 | h8054
          · linarith only [h7981, h7982, h8054, hlam]
          · linarith only [h5235, h7979, h8054, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8057 | h8057
      · linarith only [h0, h7104, h7981, h8057, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8059 | h8059
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8060 | h8060
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8061 | h8061
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8062 | h8062
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8063 | h8063
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8064 | h8064
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8065 | h8065
                    · rcases h1bigk with h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c | h8066c
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h0, hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h5235, hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h6110, hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h6504, hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h7981, hlam, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h8057, hlam, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h6504, h8057, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h7981, hc01, hc23, hlam, hphi, ht12, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h7981, hc12, hc23, hlam, hphi, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h6110, h7981, hc01, hc23, hlam, hphi, ht12, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h6504, h7981, hc01, hc23, hlam, hphi, ht12, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h6504, h8057, h8059, hc01, hc24, hlam, hphi, ht12, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h8060, hlam, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h6504, h7981, h8060, hc01, hc23, hlam, hphi, ht12, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h8059, hc01, hc12, hlam, hphi, p8066_1]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h8059, hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h8061, hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [h8062, hlam, p8066_0]
                      · have p8066_0 := h8066c.1
                        have p8066_1 := h8066c.2.1
                        have p8066_2 := h8066c.2.2.1
                        have p8066_3 := h8066c.2.2.2
                        linarith only [hlam, p8066_0]
                    · rcases h1bigk with h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h0, hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h5235, hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h6110, hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h6504, hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8057, h8063, hc01, hc23, hlam, hphi, ht12, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h7981, hlam, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8057, hlam, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8057, h8063, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h7981, hc01, hc23, hlam, hphi, ht12, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h7981, hc12, hc23, hlam, hphi, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h6110, h7981, hc01, hc23, hlam, hphi, ht12, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h6504, h7981, hc01, hc23, hlam, hphi, ht12, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8057, h8059, h8063, h8064, h8065, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8060, hlam, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h6504, h8057, h8063, hc01, hc23, hlam, hphi, ht12, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8092_1]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8059, hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8061, hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [h8062, hlam, p8092_0]
                      · have p8092_0 := h8092c.1
                        have p8092_1 := h8092c.2.1
                        have p8092_2 := h8092c.2.2.1
                        have p8092_3 := h8092c.2.2.2
                        linarith only [hlam, p8092_0]
                  · linarith only [h6110, h7980, h8057, h8064, hlam]
                · linarith only [h5235, h7979, h7981, h8063, hlam]
              · linarith only [h5235, h6110, h7979, h7980, h8062, hc01, hc13, hlam, hphi]
            · linarith only [h7981, h8059, h8061, hlam]
          · linarith only [h5235, h7979, h8060, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8123 | h8123
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8124 | h8124
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8125 | h8125
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8126 | h8126
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8127 | h8127
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8128 | h8128
                    · rcases h1bigk with h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c | h8129c
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h0, hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h5235, hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h6110, hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h6504, hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h7981, hlam, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h8057, hlam, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h8059, hlam, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h7981, hc12, hc23, hlam, hphi, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h6110, h7981, hc01, hc23, hlam, hphi, ht12, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h0, h7981, h8059, hc01, hc23, hlam, hphi, ht12, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h0, h8057, h8126, hc01, hc23, hlam, hphi, ht12, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h8123, hlam, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h0, h8057, h8059, h8126, hc01, hc23, hlam, hphi, ht12, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h0, h8059, hc01, hc25, hlam, hphi, ht12, p8129_1]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h8124, hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [h8125, hlam, p8129_0]
                      · have p8129_0 := h8129c.1
                        have p8129_1 := h8129c.2.1
                        have p8129_2 := h8129c.2.2.1
                        have p8129_3 := h8129c.2.2.2
                        linarith only [hlam, p8129_0]
                    · rcases h1bigk with h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c | h8155c
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h0, hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h5235, hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h6110, hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h6504, hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h7981, hlam, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h8057, hlam, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h8059, hlam, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h7981, hc01, hc23, hlam, hphi, ht12, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h7981, hc12, hc23, hlam, hphi, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h6110, h7981, hc01, hc23, hlam, hphi, ht12, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h6504, h7981, hc01, hc23, hlam, hphi, ht12, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h0, h8057, h8126, hc01, hc23, hlam, hphi, ht12, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h8123, hlam, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h6504, h7980, h8057, h8126, h8128, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h0, h8059, h8126, h8127, hc01, hc23, hlam, hphi, ht12, p8155_1]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h8124, hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [h8125, hlam, p8155_0]
                      · have p8155_0 := h8155c.1
                        have p8155_1 := h8155c.2.1
                        have p8155_2 := h8155c.2.2.1
                        have p8155_3 := h8155c.2.2.2
                        linarith only [hlam, p8155_0]
                  · linarith only [h5235, h6110, h7979, h7980, h7981, h8057, h8127, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h5235, h7979, h7981, h8126, hlam]
              · linarith only [h6110, h7980, h8125, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8184 | h8184
              · linarith only [h8123, h8124, h8184, hlam]
              · linarith only [h5235, h6110, h7979, h7980, h8184, hc01, hc13, hlam, hphi]
          · linarith only [h5235, h7979, h8123, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8188 | h8188
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8189 | h8189
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8190 | h8190
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8191 | h8191
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8192 | h8192
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8193 | h8193
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8194 | h8194
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8195 | h8195
                  · linarith only [h0, h7104, h7980, h8188, h8194, h8195, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h7104, h8191, h8193, h8195, hc01, hc13, hlam, hphi]
                · linarith only [h7104, h7979, h8194, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8199 | h8199
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8200 | h8200
                  · linarith only [h8189, h8193, h8200, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8202 | h8202
                    · linarith only [h7104, h8188, h8189, h8193, h8199, h8202, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h1bigk with h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h0, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h5235, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h6110, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h6504, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8192, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h0, h7104, h8189, hc01, hc12, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8188, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h0, h7104, h8188, h8189, hc01, hc12, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h6504, h8188, hc01, hc12, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8189, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8191, hlam, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8193, hlam, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8190, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8192, hlam, p8204_0]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [h8193, hc14, hc45, hlam, hphi, p8204_1]
                      · have p8204_0 := h8204c.1
                        have p8204_1 := h8204c.2.1
                        have p8204_2 := h8204c.2.2.1
                        have p8204_3 := h8204c.2.2.2
                        linarith only [hlam, p8204_0]
                · linarith only [h7104, h7979, h8199, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8231 | h8231
              · linarith only [h6110, h7980, h8191, h8192, h8231, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8233 | h8233
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8234 | h8234
                  · linarith only [h6110, h8231, h8233, h8234, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8236 | h8236
                    · linarith only [h0, h7104, h8189, h8231, h8236, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h1bigk with h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c | h8238c
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h0, hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h5235, hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h6110, hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h6504, hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h5235, h7979, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h0, h7104, h8189, hc01, hc12, hlam, hphi, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h8188, hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h0, h7104, h8189, h8192, h8236, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h8192, hlam, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h8189, hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h8191, hlam, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h8231, hlam, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h8190, hlam, p8238_0]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h5235, h8192, h8236, hc03, hc45, hlam, hphi, ht34, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [h0, h7104, h8189, h8192, h8236, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8238_1]
                      · have p8238_0 := h8238c.1
                        have p8238_1 := h8238c.2.1
                        have p8238_2 := h8238c.2.2.1
                        have p8238_3 := h8238c.2.2.2
                        linarith only [hlam, p8238_0]
                · linarith only [h5235, h7979, h8192, h8233, hc23, hc35, hlam, hphi]
          · linarith only [h5235, h7979, h8191, hlam]
        · linarith only [h0, h7104, h8189, h8190, hc01, hc25, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8267 | h8267
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8268 | h8268
          · linarith only [h8188, h8189, h8268, hlam]
          · linarith only [h5235, h7979, h8268, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8271 | h8271
          · linarith only [h8188, h8189, h8271, hlam]
          · linarith only [h5235, h7979, h8271, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8274 | h8274
      · linarith only [h0, h7104, h8188, h8274, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8276 | h8276
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8277 | h8277
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8278 | h8278
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8279 | h8279
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8280 | h8280
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8281 | h8281
                  · linarith only [h0, h7104, h7980, h8274, h8276, h8280, h8281, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h8274, h8276, h8277, h8279, h8281, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h7104, h7980, h8188, h8277, h8279, h8280, hc02, hc34, hlam, hphi, ht23]
              · linarith only [h8274, h8276, h8279, hlam]
            · linarith only [h8188, h8276, h8278, hlam]
          · linarith only [h5235, h7979, h8277, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8288 | h8288
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8289 | h8289
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8290 | h8290
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8291 | h8291
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8292 | h8292
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8293 | h8293
                    · linarith only [h7979, h7980, h8293, hlam]
                    · rcases h1bigk with h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c | h8295c
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h0, hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h5235, hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h6110, hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h6504, hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8276, h8291, h8292, hc01, hc23, hlam, hphi, ht12, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8188, hlam, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8274, hlam, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8276, hlam, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8188, hc01, hc23, hlam, hphi, ht12, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8188, hc12, hc23, hlam, hphi, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h6110, h8188, hc01, hc23, hlam, hphi, ht12, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h0, h8188, h8276, hc01, hc23, hlam, hphi, ht12, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h0, h8274, h8291, hc01, hc23, hlam, hphi, ht12, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8288, hlam, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h0, h8274, h8276, h8291, hc01, hc23, hlam, hphi, ht12, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h0, h8276, h8291, h8292, hc01, hc23, hlam, hphi, ht12, p8295_1]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8289, hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [h8290, hlam, p8295_0]
                      · have p8295_0 := h8295c.1
                        have p8295_1 := h8295c.2.1
                        have p8295_2 := h8295c.2.2.1
                        have p8295_3 := h8295c.2.2.2
                        linarith only [hlam, p8295_0]
                  · linarith only [h0, h8274, h8292, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h5235, h7979, h8188, h8291, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8323 | h8323
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8324 | h8324
                  · linarith only [h6110, h8290, h8323, h8324, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h8274, h8324, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h7979, h8188, h8323, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8328 | h8328
              · linarith only [h6110, h7980, h8288, h8289, h8328, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8330 | h8330
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8331 | h8331
                  · linarith only [h6110, h8328, h8330, h8331, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h8274, h8331, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h5235, h7979, h8289, h8330, hc23, hc35, hlam, hphi]
          · linarith only [h5235, h7979, h8288, hlam]

end R2N4
