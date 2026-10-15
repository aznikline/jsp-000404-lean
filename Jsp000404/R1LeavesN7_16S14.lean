import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S12
import Jsp000404.R1LeavesN7_16S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10070 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10497 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 3 4 (by decide) (by decide) with h10722 | h10722
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10723 | h10723
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10724 | h10724
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10725 | h10725
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10726 | h10726
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10727 | h10727
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10728 | h10728
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10729 | h10729
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10730 | h10730
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10731 | h10731
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10732 | h10732
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10733 | h10733
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10734 | h10734
                          · rcases h1bigk with h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c | h10735c
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h0, hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h6137, hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h7252, hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h8021, hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h6137, hc01, hc12, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10497, h10727, h10730, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10497, h10727, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10725, hlam, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10725, h7252, hc01, hc12, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h0, h10497, h10725, h10727, hc01, hc12, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10726, hlam, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10728, hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h0, h10497, h10725, h10727, h10728, hc01, hc12, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10727, hlam, p10735_1]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10729, hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [h10730, hlam, p10735_0]
                            · have p10735_0 := h10735c.1
                              have p10735_1 := h10735c.2.1
                              have p10735_2 := h10735c.2.2.1
                              have p10735_3 := h10735c.2.2.2
                              linarith only [hlam, p10735_0]
                          · rcases h1bigk with h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c | h10761c
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h0, hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h6137, hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h7252, hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h8021, hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h6137, hc01, hc12, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h7252, hc01, hc12, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h8021, hc01, hc12, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h10725, hlam, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h10725, h7252, hc01, hc12, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h0, h10497, h10725, h10727, hc01, hc12, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h10726, hlam, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h10728, hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h0, h10497, h10725, h10727, h10728, hc01, hc12, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h10727, hlam, p10761_1]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h10729, hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [h10730, hlam, p10761_0]
                            · have p10761_0 := h10761c.1
                              have p10761_1 := h10761c.2.1
                              have p10761_2 := h10761c.2.2.1
                              have p10761_3 := h10761c.2.2.2
                              linarith only [hlam, p10761_0]
                        · linarith only [h10070, h10724, h10733, hlam]
                      · linarith only [h10723, h10732, h8693, hlam]
                    · linarith only [h10722, h10731, h8693, hlam]
                  · linarith only [h10722, h10724, h10725, h10730, h7252, h8693, hc01, hc12, hlam, hphi]
                · linarith only [h10723, h10725, h10729, h6137, h8693, hc01, hc12, hlam, hphi]
              · linarith only [h10722, h10725, h10728, h8693, hlam]
            · linarith only [h0, h10725, h10727, h8693, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10725, h10726, h8693, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10795 | h10795
          · linarith only [h0, h10070, h10725, h10795, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10797 | h10797
            · linarith only [h0, h10497, h10725, h10797, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10799 | h10799
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10800 | h10800
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10801 | h10801
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10802 | h10802
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10803 | h10803
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10804 | h10804
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10805 | h10805
                          · rcases h1bigk with h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c | h10806c
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h0, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h6137, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h7252, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h8021, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10797, h10802, h10804, hc01, hc23, hlam, hphi, ht12, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10725, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10795, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10797, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10725, hc12, hc23, hlam, hphi, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h0, h10725, h10797, h10801, hc01, hc23, hlam, hphi, ht12, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h0, h10725, h10797, hc01, hc23, hlam, hphi, ht12, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h0, h10795, h10802, hc01, hc23, hlam, hphi, ht12, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10799, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h0, h10795, h10797, h10802, hc01, hc23, hlam, hphi, ht12, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h0, h10797, h10802, h10804, hc01, hc23, hlam, hphi, ht12, p10806_1]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10800, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [h10801, hlam, p10806_0]
                            · have p10806_0 := h10806c.1
                              have p10806_1 := h10806c.2.1
                              have p10806_2 := h10806c.2.2.1
                              have p10806_3 := h10806c.2.2.2
                              linarith only [hlam, p10806_0]
                          · rcases h1bigk with h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c | h10832c
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h0, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h6137, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h7252, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h8021, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10725, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10795, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10797, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10725, hc01, hc23, hlam, hphi, ht12, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10725, hc12, hc23, hlam, hphi, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10724, h10725, h10805, h7252, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10725, h8021, hc01, hc23, hlam, hphi, ht12, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h0, h10795, hc01, hc24, hlam, hphi, ht12, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10799, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h0, h10725, h10797, h10799, hc01, hc23, hlam, hphi, ht12, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p10832_1]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10800, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [h10801, hlam, p10832_0]
                            · have p10832_0 := h10832c.1
                              have p10832_1 := h10832c.2.1
                              have p10832_2 := h10832c.2.2.1
                              have p10832_3 := h10832c.2.2.2
                              linarith only [hlam, p10832_0]
                        · linarith only [h0, h10070, h10722, h10724, h10725, h10804, h6137, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h10723, h10725, h10799, h10801, h10803, h8021, hlam]
                    · linarith only [h10722, h10725, h10802, h6137, hlam]
                  · linarith only [h10724, h10801, h7252, hlam]
                · linarith only [h10723, h10800, h6137, hlam]
              · linarith only [h10722, h10799, h6137, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10864 | h10864
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10865 | h10865
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10866 | h10866
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10867 | h10867
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10868 | h10868
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10869 | h10869
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10870 | h10870
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10871 | h10871
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10872 | h10872
                        · linarith only [h10724, h10864, h10870, h10872, h7252, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h10070, h10864, h10867, h10869, h10872, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h10723, h10864, h10871, h6137, h8693, hc01, hc12, hlam, hphi]
                    · linarith only [h10722, h10870, h8693, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10877 | h10877
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10878 | h10878
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10879 | h10879
                        · linarith only [h10869, h10879, h7252, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10881 | h10881
                          · linarith only [h10722, h10869, h10881, h7252, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases h1bigk with h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c | h10883c
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h0, hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h6137, hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h7252, hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h8021, hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h6137, hc01, hc12, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h0, h10070, h10865, hc01, hc12, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h8021, hc01, hc12, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10864, hlam, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h0, h10070, h10864, h10865, hc01, hc12, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10864, h8021, hc01, hc12, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10865, hlam, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10867, hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10869, hlam, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10866, hlam, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10868, hlam, p10883_0]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [h10869, hc14, hc45, hlam, hphi, p10883_1]
                            · have p10883_0 := h10883c.1
                              have p10883_1 := h10883c.2.1
                              have p10883_2 := h10883c.2.2.1
                              have p10883_3 := h10883c.2.2.2
                              linarith only [hlam, p10883_0]
                      · linarith only [h10723, h10878, h8693, hlam]
                    · linarith only [h10722, h10877, h8693, hlam]
                · linarith only [h10723, h10864, h10868, h6137, h8693, hc01, hc12, hlam, hphi]
              · linarith only [h10722, h10864, h10867, h8693, hlam]
            · linarith only [h0, h10864, h10866, h8693, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10864, h10865, h8693, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10915 | h10915
          · linarith only [h0, h10070, h10864, h10915, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10917 | h10917
            · linarith only [h0, h10497, h10864, h10917, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10919 | h10919
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10920 | h10920
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10921 | h10921
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10922 | h10922
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10923 | h10923
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10924 | h10924
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10925 | h10925
                          · linarith only [h10722, h10724, h10925, hlam]
                          · rcases h1bigk with h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c | h10927c
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h0, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h6137, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h7252, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h8021, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10917, h10922, h10924, hc01, hc23, hlam, hphi, ht12, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10864, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10915, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10917, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10864, hc01, hc23, hlam, hphi, ht12, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10864, hc12, hc23, hlam, hphi, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10724, h10864, h10921, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10864, h8021, hc01, hc23, hlam, hphi, ht12, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h0, h10915, h10922, hc01, hc23, hlam, hphi, ht12, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10919, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10915, h10922, h8021, hc01, hc23, hlam, hphi, ht12, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h0, h10917, h10922, h10924, hc01, hc23, hlam, hphi, ht12, p10927_1]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10920, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [h10921, hlam, p10927_0]
                            · have p10927_0 := h10927c.1
                              have p10927_1 := h10927c.2.1
                              have p10927_2 := h10927c.2.2.1
                              have p10927_3 := h10927c.2.2.2
                              linarith only [hlam, p10927_0]
                        · linarith only [h10915, h10921, h10924, hlam]
                      · linarith only [h10723, h10724, h10915, h10921, h10922, h10923, hlam]
                    · linarith only [h10722, h10864, h10922, h6137, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10956 | h10956
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10957 | h10957
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10958 | h10958
                        · linarith only [h10921, h10956, h10958, h7252, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h10915, h10958, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h10723, h10957, h6137, h8693, hc01, hc13, hlam, hphi]
                    · linarith only [h10722, h10864, h10956, h6137, hlam]
                · linarith only [h10723, h10920, h6137, hlam]
              · linarith only [h10722, h10919, h6137, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10965 | h10965
      · linarith only [h10722, h10723, h10965, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10967 | h10967
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10968 | h10968
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10969 | h10969
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10970 | h10970
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10971 | h10971
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10972 | h10972
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10973 | h10973
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10974 | h10974
                      · linarith only [h10722, h10723, h10967, h10974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h10971, h10974, h8693, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h10722, h10723, h10967, h10971, h10973, h8693, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10978 | h10978
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10979 | h10979
                      · linarith only [h10722, h10723, h10967, h10979, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h10971, h10979, h8693, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h10722, h10967, h10978, h6137, h8693, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10983 | h10983
                  · linarith only [h0, h10070, h10965, h10970, h10971, h10983, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10985 | h10985
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10986 | h10986
                      · linarith only [h10971, h10986, h6137, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10988 | h10988
                        · linarith only [h10967, h10971, h10983, h10985, h10988, h7252, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10990 | h10990
                          · linarith only [h10070, h10722, h10967, h10968, h10971, h10983, h10990, h8693, hc02, hc35, hlam, hphi, ht23]
                          · rcases h1bigk with h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c | h10992c
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h0, hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h6137, hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h7252, hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h8021, hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h6137, hc01, hc12, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h0, h10070, h10968, hc01, hc12, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h8021, hc01, hc12, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h10967, hlam, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h0, h10070, h10967, h10968, hc01, hc12, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h10971, hlam, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h10968, hlam, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h10970, hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hlam, p10992_0]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h10983, hlam, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h10969, hlam, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h10971, h10990, hc13, hc45, hlam, hphi, ht34, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [h0, h10070, h10968, h10971, h10990, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10992_1]
                            · have p10992_0 := h10992c.1
                              have p10992_1 := h10992c.2.1
                              have p10992_2 := h10992c.2.2.1
                              have p10992_3 := h10992c.2.2.2
                              linarith only [hlam, p10992_0]
                    · linarith only [h10722, h10985, h8693, hlam]
              · linarith only [h10722, h10970, h6137, h8693, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h10967, h10969, h8693, hc02, hc25, hlam, hphi]
          · linarith only [h0, h10967, h10968, h8693, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11022 | h11022
          · linarith only [h0, h10070, h10967, h11022, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11024 | h11024
            · linarith only [h0, h10497, h10967, h11024, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11026 | h11026
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11027 | h11027
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11028 | h11028
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11029 | h11029
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11030 | h11030
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11031 | h11031
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11032 | h11032
                          · linarith only [h0, h10070, h10722, h10965, h10967, h11032, h6137, hc01, hc23, hlam, hphi, ht12]
                          · rcases h1bigk with h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h0, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h6137, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h7252, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h8021, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11024, h11029, h11031, hc01, hc23, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10967, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11022, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11024, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10967, hc01, hc23, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10967, hc12, hc23, hlam, hphi, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10722, h10723, h10967, h11028, h11032, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10967, h8021, hc01, hc23, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h0, h11022, h11029, hc01, hc23, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11026, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10722, h10723, h11022, h11027, h11029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h0, h11024, h11029, h11031, hc01, hc23, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11027, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11028, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                        · linarith only [h0, h11022, h11031, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h10967, h11027, h11030, hlam]
                    · linarith only [h10722, h10723, h10967, h11027, h11029, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11063 | h11063
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11064 | h11064
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11065 | h11065
                        · linarith only [h0, h11022, h11028, h11065, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h11022, h11065, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h10967, h11027, h11064, hc01, hc15, hlam, hphi]
                    · linarith only [h10722, h10723, h10967, h11027, h11063, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11070 | h11070
                  · linarith only [h0, h10070, h10965, h11026, h11027, h11070, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11072 | h11072
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11073 | h11073
                      · linarith only [h11027, h11073, h6137, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h10967, h11073, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h10722, h10967, h11072, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h10722, h11026, h6137, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h11078 | h11078
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11079 | h11079
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11080 | h11080
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11081 | h11081
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11082 | h11082
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11083 | h11083
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11084 | h11084
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11085 | h11085
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11086 | h11086
                    · linarith only [h10722, h11078, h11080, h11086, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h11080, h11083, h11086, h8693, hc01, hc12, hlam, hphi]
                  · linarith only [h10722, h11078, h11079, h11080, h11083, h11085, h7252, hc01, hc12, hlam, hphi]
                · linarith only [h10722, h11083, h11084, hc03, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11091 | h11091
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11092 | h11092
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11093 | h11093
                    · linarith only [h11083, h11093, h6137, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11095 | h11095
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11096 | h11096
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11097 | h11097
                          · rcases h1bigk with h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c | h11098c
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h0, hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h6137, hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h7252, hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h8021, hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h0, h10497, h11082, h11091, hc01, hc12, hlam, hphi, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h0, h10497, h11082, h11083, h11091, hc01, hc12, hlam, hphi, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h0, h10497, h11082, hc01, hc12, hlam, hphi, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11080, hlam, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11083, hlam, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h0, h10497, h11082, h11083, hc01, hc34, hlam, hphi, ht12, ht23, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11083, hc01, hc34, hlam, hphi, ht12, ht23, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11081, hlam, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11083, hc13, hc34, hlam, hphi, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h0, h10497, h11082, h11083, hc01, hc34, hlam, hphi, ht12, ht23, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11082, hlam, p11098_1]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11091, hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [h11092, hlam, p11098_0]
                            · have p11098_0 := h11098c.1
                              have p11098_1 := h11098c.2.1
                              have p11098_2 := h11098c.2.2.1
                              have p11098_3 := h11098c.2.2.2
                              linarith only [hlam, p11098_0]
                          · linarith only [h10070, h11079, h11083, h11097, h7252, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h10070, h10722, h11078, h11079, h11096, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h11078, h11095, h8693, hlam]
                  · linarith only [h10070, h11079, h11092, h7252, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h11078, h11080, h11091, h8693, hlam]
            · linarith only [h0, h10070, h11081, h11082, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11080, h11081, h8693, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11131 | h11131
          · linarith only [h0, h10070, h11080, h11131, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11133 | h11133
            · linarith only [h0, h10497, h11080, h11133, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11135 | h11135
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11136 | h11136
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11137 | h11137
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11138 | h11138
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11139 | h11139
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11140 | h11140
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11141 | h11141
                          · rcases h1bigk with h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c | h11142c
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h0, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h6137, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h7252, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h8021, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11133, h11138, h11140, hc01, hc23, hlam, hphi, ht12, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11080, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11131, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11133, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11080, hc01, hc23, hlam, hphi, ht12, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11080, hc12, hc23, hlam, hphi, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h0, h11080, h11133, h11137, hc01, hc23, hlam, hphi, ht12, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h0, h11080, h11133, hc01, hc23, hlam, hphi, ht12, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h0, h11131, h11138, hc01, hc23, hlam, hphi, ht12, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11135, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h0, h11131, h11133, h11138, hc01, hc23, hlam, hphi, ht12, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h0, h11133, h11138, h11140, hc01, hc23, hlam, hphi, ht12, p11142_1]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11136, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [h11137, hlam, p11142_0]
                            · have p11142_0 := h11142c.1
                              have p11142_1 := h11142c.2.1
                              have p11142_2 := h11142c.2.2.1
                              have p11142_3 := h11142c.2.2.2
                              linarith only [hlam, p11142_0]
                          · linarith only [h10722, h11078, h11079, h11141, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10722, h11078, h11079, h11080, h11131, h11135, h11140, h7252, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h10722, h11078, h11080, h11135, h11139, hlam]
                    · linarith only [h11080, h11135, h11138, hlam]
                  · linarith only [h10722, h11078, h11079, h11080, h11135, h11137, h7252, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10722, h11078, h11135, h11136, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11174 | h11174
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11175 | h11175
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11176 | h11176
                    · linarith only [h0, h11133, h11135, h11174, h11176, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11080, h11176, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h10722, h11078, h11079, h11175, h7252, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11078, h11174, h6137, hlam]
      · linarith only [h10722, h11078, h11079, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11182 | h11182
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11183 | h11183
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11184 | h11184
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11185 | h11185
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11186 | h11186
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11187 | h11187
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11188 | h11188
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11189 | h11189
                    · linarith only [h0, h10722, h11183, h11189, h8693, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h11183, h11186, h11189, h8693, hc01, hc12, hlam, hphi]
                  · linarith only [h11182, h11188, h7252, hlam]
                · linarith only [h0, h10722, h11186, h11187, h8693, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11194 | h11194
                · linarith only [h0, h11078, h11186, h11194, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11196 | h11196
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11197 | h11197
                    · linarith only [h0, h10722, h11183, h11197, h8693, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11199 | h11199
                      · linarith only [h11183, h11194, h11199, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11201 | h11201
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11202 | h11202
                          · rcases h1bigk with h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c | h11203c
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h0, hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h6137, hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h7252, hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h8021, hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h6137, hc01, hc12, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h7252, hc01, hc12, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h0, h10497, h11185, hc01, hc12, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h11183, hlam, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h11186, hlam, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h11194, hlam, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h11184, hlam, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h11186, hc13, hc34, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h0, h11183, h11186, h11194, h8693, hc01, hc34, hlam, hphi, ht12, ht23, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h11185, hlam, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h0, h11183, h11194, h11202, h8693, hc01, hc34, hlam, hphi, ht12, ht23, p11203_1]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [h11196, hlam, p11203_0]
                            · have p11203_0 := h11203c.1
                              have p11203_1 := h11203c.2.1
                              have p11203_2 := h11203c.2.2.1
                              have p11203_3 := h11203c.2.2.2
                              linarith only [hlam, p11203_0]
                          · linarith only [h10070, h11182, h11186, h11202, h7252, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h10070, h11182, h11201, hlam]
                  · linarith only [h10070, h11182, h11196, h7252, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h10070, h11184, h11185, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11183, h11184, h8693, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11234 | h11234
          · linarith only [h0, h10070, h11183, h11234, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11236 | h11236
            · linarith only [h0, h10497, h11183, h11236, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11238 | h11238
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11239 | h11239
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11240 | h11240
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11241 | h11241
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11242 | h11242
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11243 | h11243
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11244 | h11244
                          · rcases h1bigk with h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h6137, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h7252, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h8021, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11236, h11241, h11243, hc01, hc23, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11183, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11234, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11236, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11183, hc12, hc23, hlam, hphi, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h11183, h11236, h11240, hc01, hc23, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h11183, h11236, hc01, hc23, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h11234, h11241, hc01, hc23, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11238, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h11078, h11234, h11239, h11241, h8693, hc01, hc23, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h11236, h11241, h11243, hc01, hc23, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11239, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11240, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                          · linarith only [h0, h10722, h11182, h11234, h11241, h11244, h7252, h8693, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h11182, h11234, h11243, h7252, hlam]
                      · linarith only [h0, h10722, h11183, h11238, h11242, h8693, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11078, h11183, h11239, h11241, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11182, h11240, h7252, hlam]
                · linarith only [h0, h10722, h11238, h11239, h8693, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11277 | h11277
                · linarith only [h0, h11078, h11238, h11277, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11279 | h11279
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11280 | h11280
                    · linarith only [h11238, h11280, h6137, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11183, h11280, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11182, h11279, h7252, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11284 | h11284
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11285 | h11285
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11286 | h11286
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11287 | h11287
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11288 | h11288
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11289 | h11289
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11290 | h11290
                    · linarith only [h0, h10722, h11284, h11290, h8693, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h11287, h11290, h8693, hc01, hc13, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11293 | h11293
                    · linarith only [h0, h10722, h11284, h11293, h8693, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h11287, h11289, h11293, h8693, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h10722, h11287, h11288, h8693, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11297 | h11297
                · linarith only [h0, h11078, h11287, h11297, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11299 | h11299
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11300 | h11300
                    · linarith only [h11287, h11300, h6137, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11302 | h11302
                      · linarith only [h11284, h11297, h11302, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11304 | h11304
                        · linarith only [h0, h10722, h11182, h11285, h11304, h8693, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h10070, h11299, h11304, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11307 | h11307
                    · linarith only [h0, h10722, h11284, h11297, h11307, h8693, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11309 | h11309
                      · linarith only [h0, h11078, h11284, h11287, h11299, h11309, h8693, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11311 | h11311
                        · linarith only [h11287, h11299, h11311, h6137, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11313 | h11313
                          · linarith only [h0, h11284, h11287, h11299, h11313, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h11284, h11287, h11313, h8693, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h11284, h11286, h8693, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11284, h11285, h8693, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11318 | h11318
          · linarith only [h0, h10070, h11284, h11318, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11320 | h11320
            · linarith only [h0, h10497, h11284, h11320, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11322 | h11322
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11323 | h11323
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11324 | h11324
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11325 | h11325
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11326 | h11326
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11327 | h11327
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11328 | h11328
                          · linarith only [h0, h10722, h11182, h11322, h11328, h8693, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h10722, h11324, h11328, h8693, hc01, hc14, hlam, hphi]
                        · linarith only [h11318, h11324, h11327, hlam]
                      · linarith only [h11284, h11323, h11326, hlam]
                    · linarith only [h0, h11078, h11284, h11323, h11325, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11334 | h11334
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11335 | h11335
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11336 | h11336
                        · linarith only [h11324, h11336, h7252, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h11318, h11336, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h11323, h11335, h8693, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h11078, h11284, h11323, h11334, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h10722, h11322, h11323, h8693, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11342 | h11342
                · linarith only [h0, h11078, h11322, h11342, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11344 | h11344
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11345 | h11345
                    · linarith only [h11322, h11345, h6137, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11284, h11345, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11348 | h11348
                    · linarith only [h11322, h11348, h6137, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11284, h11348, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10070 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 2 5 (by decide) (by decide) with h10497 | h10497
  · exact r1l7_21_15_H_I_L_I_s10_x1_x1_x0 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h10070 h10497
  · exact r1l7_21_15_H_I_L_I_s10_x1_x1_x1 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h10070 h10497

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 2 4 (by decide) (by decide) with h10070 | h10070
  · exact r1l7_21_15_H_I_L_I_s10_x1_x0 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h10070
  · exact r1l7_21_15_H_I_L_I_s10_x1_x1 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h10070

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 2 3 (by decide) (by decide) with h8693 | h8693
  · exact r1l7_21_15_H_I_L_I_s10_x0 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693
  · exact r1l7_21_15_H_I_L_I_s10_x1 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693

end R2N4
