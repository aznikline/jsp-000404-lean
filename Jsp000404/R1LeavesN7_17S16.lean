import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S11
import Jsp000404.R1LeavesN7_17S14
import Jsp000404.R1LeavesN7_17S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10507 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 3 4 (by decide) (by decide) with h10720 | h10720
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10721 | h10721
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10722 | h10722
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10723 | h10723
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10724 | h10724
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10725 | h10725
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10726 | h10726
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10727 | h10727
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10728 | h10728
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10729 | h10729
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10730 | h10730
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10731 | h10731
                        · rcases h0bigk with h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c | h10732c
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h0, hlam, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h6421, hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h7464, hlam, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h8188, hlam, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10507, h10725, h10727, hc01, hc14, hlam, hphi, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h8818, hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10104, hlam, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10507, hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10723, h8818, hc01, hc12, hlam, hphi, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10723, h8818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10723, h8818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h0, h10507, h10723, h8818, hc01, hc12, hlam, hphi, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h0, h10104, h10723, h10728, hc01, hc12, hlam, hphi, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10720, hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h0, h10104, h10507, h10723, h10728, hc01, hc12, hlam, hphi, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10727, h8188, hc01, hc14, hlam, hphi, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h0, h10507, hc01, hc25, hlam, hphi, ht12, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10721, hlam, p10732_0]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [h10722, hlam, p10732_1]
                          · have p10732_0 := h10732c.1
                            have p10732_1 := h10732c.2.1
                            have p10732_2 := h10732c.2.2.1
                            have p10732_3 := h10732c.2.2.2
                            linarith only [hlam, p10732_0]
                        · rcases h0bigk with h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c | h10758c
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h0, hlam, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h6421, hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h7464, hlam, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h8188, hlam, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h8818, hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10104, hlam, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10507, hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10723, h8818, hc01, hc12, hlam, hphi, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10723, h8818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10723, h8818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10723, h8818, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10723, h10726, h7464, hc01, hc12, hlam, hphi, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h0, h10104, h10723, h10728, hc01, hc12, hlam, hphi, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10720, hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h0, h10104, h10507, h10723, h10728, hc01, hc12, hlam, hphi, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10723, h10726, h10727, h8188, hc01, hc12, hlam, hphi, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h0, h10507, h10723, h10728, h10730, hc01, hc12, hlam, hphi, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10721, hlam, p10758_0]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [h10722, hlam, p10758_1]
                          · have p10758_0 := h10758c.1
                            have p10758_1 := h10758c.2.1
                            have p10758_2 := h10758c.2.2.1
                            have p10758_3 := h10758c.2.2.2
                            linarith only [hlam, p10758_0]
                      · linarith only [h10104, h10722, h10730, hlam]
                    · linarith only [h10721, h10729, h8818, hlam]
                  · linarith only [h10720, h10728, h8818, hlam]
                · linarith only [h10720, h10722, h10727, h7464, h8818, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10720, h10723, h10726, h6421, h8818, hc01, hc12, hlam, hphi]
            · linarith only [h0, h10723, h10725, h8818, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10723, h10724, h8818, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10791 | h10791
          · linarith only [h0, h10104, h10723, h10791, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10793 | h10793
            · linarith only [h0, h10507, h10723, h10793, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10795 | h10795
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10796 | h10796
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10797 | h10797
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10798 | h10798
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10799 | h10799
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10800 | h10800
                        · rcases h0bigk with h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c | h10801c
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h0, hlam, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h6421, hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h7464, hlam, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h8188, hlam, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h0, h10793, h10797, h10799, hc01, hc23, hlam, hphi, ht12, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h8818, hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h10104, hlam, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h10507, hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h6421, hc01, hc13, hlam, hphi, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h8818, hc02, hc23, hlam, hphi, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h7464, h8818, hc01, hc23, hlam, hphi, ht12, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h0, h10507, h8818, hc01, hc23, hlam, hphi, ht12, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h0, h10104, h10797, hc01, hc23, hlam, hphi, ht12, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h10720, hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h0, h10104, h10507, h10797, hc01, hc23, hlam, hphi, ht12, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h0, h10507, h10797, h10799, hc01, hc23, hlam, hphi, ht12, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h10721, hlam, p10801_0]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [h10722, hlam, p10801_1]
                          · have p10801_0 := h10801c.1
                            have p10801_1 := h10801c.2.1
                            have p10801_2 := h10801c.2.2.1
                            have p10801_3 := h10801c.2.2.2
                            linarith only [hlam, p10801_0]
                        · rcases h0bigk with h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c | h10827c
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h0, hlam, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h6421, hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h7464, hlam, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h8188, hlam, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h0, h10793, h10797, h10799, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h8818, hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10104, hlam, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10507, hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10723, h6421, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10723, h6421, hc02, hc23, hlam, hphi, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10723, h6421, h7464, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h0, h10507, h10723, h6421, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10791, h10797, h7464, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h0, h10791, h10797, h7464, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10720, hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h0, h10507, h10791, h10797, h7464, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10793, h10797, h10799, h8188, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h0, h10793, h10797, h10799, h8188, hc01, hc23, hlam, hphi, ht12, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10721, hlam, p10827_0]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [h10722, hlam, p10827_1]
                          · have p10827_0 := h10827c.1
                            have p10827_1 := h10827c.2.1
                            have p10827_2 := h10827c.2.2.1
                            have p10827_3 := h10827c.2.2.2
                            linarith only [hlam, p10827_0]
                      · linarith only [h10722, h10791, h10799, h7464, hlam]
                    · linarith only [h10721, h10723, h10798, h6421, hlam]
                  · linarith only [h10720, h10723, h10797, h6421, hlam]
                · linarith only [h10722, h10796, h7464, hlam]
              · linarith only [h10720, h10795, h6421, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10858 | h10858
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10859 | h10859
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10860 | h10860
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10861 | h10861
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10862 | h10862
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10863 | h10863
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10864 | h10864
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10865 | h10865
                      · linarith only [h10722, h10859, h10865, h7464, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h10104, h10858, h10861, h10862, h10865, hc01, hc12, hlam, hphi]
                    · linarith only [h10721, h10864, h8818, hlam]
                  · linarith only [h10720, h10863, h8818, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10870 | h10870
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10871 | h10871
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10872 | h10872
                      · linarith only [h10859, h10862, h10872, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10874 | h10874
                        · linarith only [h10720, h10862, h10874, h7464, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c | h10876c
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h0, hlam, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h6421, hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h7464, hlam, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h8188, hlam, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10104, h10859, hc01, hc14, hlam, hphi, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h8818, hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10104, hlam, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10507, hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10858, h8818, hc01, hc12, hlam, hphi, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10858, h8818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10858, h8818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10858, h8818, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10862, h7464, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h0, h10104, h10859, h10862, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10720, hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10722, hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h0, h10507, h10858, h10871, hc01, hc12, hlam, hphi, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10721, hlam, p10876_0]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [h10507, h10858, h10871, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10876_1]
                          · have p10876_0 := h10876c.1
                            have p10876_1 := h10876c.2.1
                            have p10876_2 := h10876c.2.2.1
                            have p10876_3 := h10876c.2.2.2
                            linarith only [hlam, p10876_0]
                    · linarith only [h10721, h10871, h8818, hlam]
                  · linarith only [h0, h10720, h10862, h10870, h7464, h8818, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h10720, h10861, h6421, h8818, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h10858, h10860, h8818, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10858, h10859, h8818, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10907 | h10907
          · linarith only [h0, h10104, h10858, h10907, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10909 | h10909
            · linarith only [h0, h10507, h10858, h10909, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10911 | h10911
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10912 | h10912
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10913 | h10913
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10914 | h10914
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10915 | h10915
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10916 | h10916
                        · linarith only [h0, h10104, h10720, h10722, h10916, h6421, hc01, hc13, hlam, hphi]
                        · rcases h0bigk with h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c | h10918c
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h0, hlam, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h6421, hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h7464, hlam, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h8188, hlam, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10104, h10722, h10912, hc01, hc14, hlam, hphi, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h8818, hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10104, hlam, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10507, hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10858, h6421, hc01, hc23, hlam, hphi, ht12, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10858, h6421, hc02, hc23, hlam, hphi, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10858, h6421, h7464, hc01, hc23, hlam, hphi, ht12, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h0, h10104, h10722, h10858, h6421, hc01, hc23, hlam, hphi, ht12, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h0, h10104, h10913, hc01, hc23, hlam, hphi, ht12, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10720, hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10722, hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h0, h10507, h10913, h10915, hc01, hc23, hlam, hphi, ht12, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10721, hlam, p10918_0]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [h10722, h10912, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p10918_1]
                          · have p10918_0 := h10918c.1
                            have p10918_1 := h10918c.2.1
                            have p10918_2 := h10918c.2.2.1
                            have p10918_3 := h10918c.2.2.2
                            linarith only [hlam, p10918_0]
                      · linarith only [h10907, h10912, h10915, hlam]
                    · linarith only [h10721, h10722, h10907, h10912, h10913, h10914, hlam]
                  · linarith only [h10720, h10858, h10913, h6421, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10947 | h10947
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10948 | h10948
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10949 | h10949
                      · linarith only [h10912, h10947, h10949, h7464, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h10907, h10949, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h10721, h10948, h6421, h8818, hc01, hc13, hlam, hphi]
                  · linarith only [h10720, h10858, h10947, h6421, hlam]
              · linarith only [h10720, h10911, h6421, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10955 | h10955
      · linarith only [h10720, h10721, h10955, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10957 | h10957
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10958 | h10958
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10959 | h10959
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10960 | h10960
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10961 | h10961
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10962 | h10962
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10963 | h10963
                    · linarith only [h10720, h10721, h10957, h10963, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10965 | h10965
                      · linarith only [h0, h10104, h10955, h10962, h10963, h10965, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h10104, h10960, h10961, h10965, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h10720, h10957, h10962, h6421, h8818, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10969 | h10969
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10970 | h10970
                    · linarith only [h10720, h10721, h10957, h10970, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10972 | h10972
                      · linarith only [h10958, h10961, h10972, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10974 | h10974
                        · linarith only [h10720, h10957, h10961, h10974, h6421, h7464, hc01, hc12, hlam, hphi]
                        · rcases h0bigk with h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c | h10976c
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h0, hlam, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h6421, hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h7464, hlam, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h8188, hlam, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10104, h10969, h10970, h10974, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h8818, hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10104, hlam, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10507, hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10970, h10974, h8818, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10970, h10974, h8818, hc02, hc45, hlam, hphi, ht23, ht34, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10970, h10974, h8818, hc04, hc45, hlam, hphi, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10721, hlam, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h0, h10104, h10969, h10970, h10974, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10720, hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10955, hlam, p10976_0]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10507, h10959, hc01, hc12, hlam, hphi, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h0, h10507, h10959, hc01, hc12, hlam, hphi, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h10507, h10959, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [h0, h10104, h10507, h10959, h10969, h10970, h10974, hc01, hc04, hc12, hc45, hlam, hphi, p10976_1]
                          · have p10976_0 := h10976c.1
                            have p10976_1 := h10976c.2.1
                            have p10976_2 := h10976c.2.2.1
                            have p10976_3 := h10976c.2.2.2
                            linarith only [hlam, p10976_0]
                  · linarith only [h0, h10720, h10957, h10969, h6421, h8818, hc01, hc12, hlam, hphi]
              · linarith only [h10720, h10960, h6421, hlam]
            · linarith only [h0, h10957, h10959, h8818, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10957, h10958, h8818, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11006 | h11006
          · linarith only [h0, h10104, h10957, h11006, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11008 | h11008
            · linarith only [h0, h10507, h10957, h11008, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11010 | h11010
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11011 | h11011
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11012 | h11012
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11013 | h11013
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11014 | h11014
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11015 | h11015
                        · linarith only [h0, h10104, h10720, h10721, h10955, h11013, h11015, hc01, hc23, hlam, hphi, ht12]
                        · rcases h0bigk with h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c | h11017c
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h0, hlam, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h6421, hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h7464, hlam, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h8188, hlam, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10104, h10720, h10721, h11010, h11011, h11015, hc01, hc13, hlam, hphi, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h8818, hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10104, hlam, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10507, hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10721, h11010, h11011, h11015, hc01, hc13, hlam, hphi, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10721, h11010, h11011, h11015, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10721, h11010, h11011, h11015, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10721, hlam, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h11010, h7464, hc01, hc13, hlam, hphi, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h0, h10104, h11012, hc01, hc23, hlam, hphi, ht12, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10720, hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10955, hlam, p11017_0]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h11010, h11011, h8188, hc01, hc13, hlam, hphi, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h0, h10507, h11012, h11014, hc01, hc23, hlam, hphi, ht12, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10721, h11010, h11011, h11015, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [h10721, h11010, h11011, h11015, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p11017_1]
                          · have p11017_0 := h11017c.1
                            have p11017_1 := h11017c.2.1
                            have p11017_2 := h11017c.2.2.1
                            have p11017_3 := h11017c.2.2.2
                            linarith only [hlam, p11017_0]
                      · linarith only [h0, h10104, h10957, h11010, h11011, h11014, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h10104, h10955, h10957, h11010, h11011, h11013, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10720, h10957, h11012, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11046 | h11046
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11047 | h11047
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11048 | h11048
                      · linarith only [h0, h11006, h11011, h11048, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h11006, h11048, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h10957, h11047, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10720, h10957, h11046, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h10720, h10721, h11010, hc13, hc35, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h11054 | h11054
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11055 | h11055
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11056 | h11056
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11057 | h11057
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11058 | h11058
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11059 | h11059
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11060 | h11060
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11061 | h11061
                  · linarith only [h10720, h11054, h11056, h11061, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h11059, h11061, h8818, hc01, hc13, hlam, hphi]
                · linarith only [h11055, h11060, h7464, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11065 | h11065
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11066 | h11066
                  · linarith only [h11059, h11066, h6421, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11068 | h11068
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11069 | h11069
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11070 | h11070
                        · rcases h0bigk with h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c | h11071c
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h0, hlam, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h6421, hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h7464, hlam, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h8188, hlam, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h10507, h11056, h11068, hc01, hc13, hlam, hphi, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h8818, hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h10104, hlam, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h10507, hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h11059, h6421, hc01, hc34, hlam, hphi, ht12, ht23, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h11056, h11059, h8818, hc02, hc34, hlam, hphi, ht23, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h10720, hlam, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h0, h10507, h11056, h11059, h8818, hc01, hc34, hlam, hphi, ht12, ht23, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h10104, h11057, hc01, hc12, hlam, hphi, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h0, h10104, h11057, hc01, hc12, hlam, hphi, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h10104, h11057, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h0, h10104, h10507, h11057, hc01, hc12, hlam, hphi, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h0, h10507, h11056, h11059, h11068, hc01, hc34, hlam, hphi, ht12, ht23, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h11054, hlam, p11071_0]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [h11055, hlam, p11071_1]
                          · have p11071_0 := h11071c.1
                            have p11071_1 := h11071c.2.1
                            have p11071_2 := h11071c.2.2.1
                            have p11071_3 := h11071c.2.2.2
                            linarith only [hlam, p11071_0]
                        · linarith only [h11059, h11070, h6421, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h10104, h11054, h11055, h11059, h11069, h6421, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h11054, h11068, h8818, hlam]
                · linarith only [h10104, h11055, h11065, h7464, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h10104, h11057, h11058, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11056, h11057, h8818, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11103 | h11103
          · linarith only [h0, h10104, h11056, h11103, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11105 | h11105
            · linarith only [h0, h10507, h11056, h11105, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11107 | h11107
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11108 | h11108
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11109 | h11109
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11110 | h11110
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11111 | h11111
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11112 | h11112
                        · rcases h0bigk with h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c | h11113c
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h0, hlam, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h6421, hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h7464, hlam, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h8188, hlam, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h0, h11105, h11109, h11111, hc01, hc23, hlam, hphi, ht12, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h8818, hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h10104, hlam, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h10507, hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h10720, h11056, h11107, hc01, hc23, hlam, hphi, ht12, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h10720, h11056, h11107, hc02, hc23, hlam, hphi, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h10720, hlam, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h10720, h11056, h11107, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h0, h10104, h11109, hc01, hc23, hlam, hphi, ht12, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h10720, h11056, h11107, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h0, h10507, h10720, h11056, h11107, hc01, hc23, hlam, hphi, ht12, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h11054, h11056, h6421, hc01, hc23, hlam, hphi, ht12, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h0, h11054, h11056, h6421, hc01, hc23, hlam, hphi, ht12, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h11054, hlam, p11113_0]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [h11055, hlam, p11113_1]
                          · have p11113_0 := h11113c.1
                            have p11113_1 := h11113c.2.1
                            have p11113_2 := h11113c.2.2.1
                            have p11113_3 := h11113c.2.2.2
                            linarith only [hlam, p11113_0]
                        · linarith only [h10720, h11055, h11112, hlam]
                      · linarith only [h10720, h11054, h11055, h11103, h11111, h7464, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h10720, h11056, h11107, h11110, hc03, hc35, hlam, hphi]
                  · linarith only [h11056, h11107, h11109, hlam]
                · linarith only [h10720, h11054, h11055, h11107, h11108, h7464, hc01, hc13, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11144 | h11144
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11145 | h11145
                  · linarith only [h11107, h11145, h6421, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11056, h11145, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11055, h11144, h7464, hlam]
      · linarith only [h10720, h11054, h11055, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11150 | h11150
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11151 | h11151
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11152 | h11152
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11153 | h11153
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11154 | h11154
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11155 | h11155
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11156 | h11156
                  · linarith only [h0, h10720, h11151, h11156, h8818, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11154, h11156, h8818, hc01, hc13, hlam, hphi]
                · linarith only [h10104, h11150, h11152, h11155, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11160 | h11160
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11161 | h11161
                  · linarith only [h11154, h11161, h6421, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11163 | h11163
                    · linarith only [h0, h11054, h11151, h11154, h11163, h8818, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11165 | h11165
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11166 | h11166
                        · rcases h0bigk with h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c | h11167c
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [hlam, p11167_0]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h0, hlam, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h6421, hlam, p11167_0]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h7464, hlam, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h8188, hlam, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [hlam, p11167_0]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h8818, hlam, p11167_0]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h10104, hlam, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h10507, hlam, p11167_0]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h11154, h6421, hc01, hc34, hlam, hphi, ht12, ht23, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h11154, h6421, hc02, hc34, hlam, hphi, ht23, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [hlam, p11167_0]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h10720, hlam, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h11054, hlam, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h0, h10104, h11152, hc01, hc14, hlam, hphi, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h10720, hc03, hc34, hlam, hphi, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [hlam, p11167_0]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h10720, h8188, hc01, hc34, hlam, hphi, ht12, ht23, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h0, h10507, hc01, hc25, hlam, hphi, ht12, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h0, h11054, h8818, hc01, hc35, hlam, hphi, ht12, ht23, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [h11150, hlam, p11167_1]
                          · have p11167_0 := h11167c.1
                            have p11167_1 := h11167c.2.1
                            have p11167_2 := h11167c.2.2.1
                            have p11167_3 := h11167c.2.2.2
                            linarith only [hlam, p11167_0]
                        · linarith only [h10104, h11150, h11152, h11154, h11166, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h10104, h11150, h11165, hlam]
                · linarith only [h10104, h11150, h11152, h11160, h7464, hc01, hc12, hlam, hphi]
            · linarith only [h0, h10104, h11152, h11153, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11151, h11152, h8818, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11198 | h11198
          · linarith only [h0, h10104, h11151, h11198, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11200 | h11200
            · linarith only [h0, h10507, h11151, h11200, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11202 | h11202
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11203 | h11203
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11204 | h11204
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11205 | h11205
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11206 | h11206
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11207 | h11207
                        · rcases h0bigk with h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c | h11208c
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [hlam, p11208_0]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h0, hlam, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h6421, hlam, p11208_0]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h7464, hlam, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h8188, hlam, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h0, h11200, h11204, h11206, hc01, hc23, hlam, hphi, ht12, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [hlam, p11208_0]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h8818, hlam, p11208_0]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h10104, hlam, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h10507, hlam, p11208_0]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h11151, h6421, hc01, hc23, hlam, hphi, ht12, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h11151, h6421, hc02, hc23, hlam, hphi, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [hlam, p11208_0]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h10720, hlam, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h11054, hlam, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h10720, h11151, h11202, hc01, hc23, hlam, hphi, ht12, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h0, h10720, h11151, h11202, hc01, hc23, hlam, hphi, ht12, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h10720, h11151, h11202, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [hlam, p11208_0]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h10720, h11151, h11202, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h0, h10507, h11204, h11206, hc01, hc23, hlam, hphi, ht12, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h0, h11054, h11151, h11202, h11207, h8818, hc01, hc23, hlam, hphi, ht12, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [h11150, hlam, p11208_1]
                          · have p11208_0 := h11208c.1
                            have p11208_1 := h11208c.2.1
                            have p11208_2 := h11208c.2.2.1
                            have p11208_3 := h11208c.2.2.2
                            linarith only [hlam, p11208_0]
                        · linarith only [h10720, h11150, h11207, hlam]
                      · linarith only [h0, h10104, h10720, h11150, h11151, h11202, h11206, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h10720, h11151, h11202, h11205, h8818, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h11151, h11202, h11204, hlam]
                · linarith only [h10720, h11150, h11202, h11203, h7464, hc01, hc13, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11239 | h11239
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11240 | h11240
                  · linarith only [h11202, h11240, h6421, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11151, h11240, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11150, h11239, h7464, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11244 | h11244
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11245 | h11245
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11246 | h11246
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11247 | h11247
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11248 | h11248
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11249 | h11249
                  · linarith only [h0, h10720, h11244, h11249, h8818, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11244, h11247, h11249, h8818, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11252 | h11252
                  · linarith only [h0, h10720, h11244, h11252, h8818, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11247, h11248, h11252, h8818, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11255 | h11255
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11256 | h11256
                  · linarith only [h11247, h11256, h6421, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11258 | h11258
                    · linarith only [h0, h11054, h11244, h11258, h8818, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11260 | h11260
                      · linarith only [h0, h10720, h11150, h11245, h11260, h8818, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h10104, h11247, h11255, h11260, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11263 | h11263
                  · linarith only [h0, h10720, h11244, h11263, h8818, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11265 | h11265
                    · linarith only [h0, h11054, h11244, h11247, h11255, h11265, h8818, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11267 | h11267
                      · linarith only [h11247, h11255, h11267, h6421, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11269 | h11269
                        · linarith only [h0, h11244, h11247, h11255, h11269, h8818, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h11244, h11247, h11269, h8818, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h11244, h11246, h8818, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11244, h11245, h8818, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11274 | h11274
          · linarith only [h0, h10104, h11244, h11274, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11276 | h11276
            · linarith only [h0, h10507, h11244, h11276, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11278 | h11278
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11279 | h11279
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11280 | h11280
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11281 | h11281
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11282 | h11282
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11283 | h11283
                        · linarith only [h0, h10720, h11150, h11244, h11278, h11283, h8818, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h10720, h11244, h11278, h11279, h11283, h8818, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h10104, h11244, h11278, h11279, h11282, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h10720, h11150, h11244, h11278, h11279, h11281, h8818, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10720, h11150, h11244, h11278, h11279, h11280, h8818, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11289 | h11289
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11290 | h11290
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11291 | h11291
                      · linarith only [h11279, h11291, h7464, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h11274, h11291, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h10720, h11244, h11278, h11290, h8818, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h11244, h11278, h11289, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11296 | h11296
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11297 | h11297
                  · linarith only [h11278, h11297, h6421, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11244, h11297, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11300 | h11300
                  · linarith only [h0, h11244, h11278, h11300, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11244, h11300, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 2 5 (by decide) (by decide) with h10507 | h10507
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h10104 h10507
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h10104 h10507

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 2 4 (by decide) (by decide) with h10104 | h10104
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h10104
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818 h10104

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 2 3 (by decide) (by decide) with h8818 | h8818
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188 h8818

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 1 5 (by decide) (by decide) with h8188 | h8188
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x0 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188
  · exact r1l7_20_12_14_H_I_L_I_L_I_s9_x1 m hb0 hb2 hb4 hg0 hg6421 hg7464 h8188

end R2N4
