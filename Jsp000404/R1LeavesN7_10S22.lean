import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S19
import Jsp000404.R1LeavesN7_10S20
import Jsp000404.R1LeavesN7_10S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10432000 in
set_option maxHeartbeats 10432000 in
theorem r1l7_12_24_L_I_H_I_s7_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h12751 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h13259 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  rcases m.htr 0 3 4 (by decide) (by decide) with h13565 | h13565
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13566 | h13566
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13567 | h13567
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13568 | h13568
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13569 | h13569
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13570 | h13570
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13571 | h13571
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13572 | h13572
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13573 | h13573
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13574 | h13574
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13575 | h13575
                      · rcases h2bigk with h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c | h13576c
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h8886, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h12751, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h13259, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          rcases p13576_3 (m.d 0 2) (by simp) with h13582 | h13582
                          · linarith only [h0, h13582, hlam]
                          · rcases p13576_3 (m.d 1 2) (by simp) with h13584 | h13584
                            · rcases p13576_3 (m.d 2 3) (by simp) with h13585 | h13585
                              · linarith only [h13567, h13585, hlam]
                              · linarith only [h13585, h8886, hlam]
                            · linarith only [h0, h13584, hlam]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h13259, h13572, h13574, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h12751, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h13259, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h13567, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h13567, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h12751, h13567, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h13259, h13567, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h13568, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h13568, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h13572, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h13259, h13568, hc01, hc14, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h0, h13569, hc01, hc12, hlam, hphi, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h13569, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h13573, hlam, p13576_0]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [h13574, hlam, p13576_1]
                        · have p13576_0 := h13576c.1
                          have p13576_1 := h13576c.2.1
                          have p13576_2 := h13576c.2.2.1
                          have p13576_3 := h13576c.2.2.2
                          linarith only [hlam, p13576_0]
                      · rcases h2bigk with h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h8886, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h12751, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h13259, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          rcases p13608_3 (m.d 0 2) (by simp) with h13614 | h13614
                          · linarith only [h0, h13614, hlam]
                          · rcases p13608_3 (m.d 1 2) (by simp) with h13616 | h13616
                            · rcases p13608_3 (m.d 2 3) (by simp) with h13617 | h13617
                              · linarith only [h13567, h13617, hlam]
                              · linarith only [h13617, h8886, hlam]
                            · linarith only [h0, h13616, hlam]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, h8886, hc01, hc12, hlam, hphi, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h12751, h13566, h13575, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, h13259, hc01, hc12, hlam, hphi, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, h13567, hc01, hc12, hlam, hphi, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h13567, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h12751, h13566, h13567, h13575, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, h13259, h13567, hc01, hc12, hlam, hphi, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, h13568, hc01, hc12, hlam, hphi, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h13568, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h13572, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, h13259, h13567, h13572, hc01, hc12, hlam, hphi, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h0, h13569, hc01, hc12, hlam, hphi, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h13569, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h13573, hlam, p13608_0]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [h13574, hlam, p13608_1]
                        · have p13608_0 := h13608c.1
                          have p13608_1 := h13608c.2.1
                          have p13608_2 := h13608c.2.2.1
                          have p13608_3 := h13608c.2.2.2
                          linarith only [hlam, p13608_0]
                    · linarith only [h0, h12751, h13566, h13570, h13574, h6874, hc01, hc13, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13641 | h13641
                    · linarith only [h13572, h13573, h13641, hlam]
                    · linarith only [h0, h12751, h13565, h13566, h13573, h13641, h8886, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h13565, h13572, h8886, hlam]
              · linarith only [h13566, h13571, h6874, hlam]
            · linarith only [h13565, h13567, h13570, h8886, hlam]
          · linarith only [h0, h13567, h13569, h8886, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h13567, h13568, h8886, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13649 | h13649
        · linarith only [h0, h12751, h13567, h13649, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13651 | h13651
          · linarith only [h0, h13259, h13567, h13651, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13653 | h13653
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13654 | h13654
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13655 | h13655
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13656 | h13656
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13657 | h13657
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13658 | h13658
                      · rcases h2bigk with h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c | h13659c
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h8886, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h12751, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13259, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, h13651, h13655, h13657, hc01, hc23, hlam, hphi, ht12, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13567, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13649, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13651, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          rcases p13659_3 (m.d 0 2) (by simp) with h13670 | h13670
                          · linarith only [h13670, hlam, p13659_0]
                          · rcases p13659_3 (m.d 1 2) (by simp) with h13672 | h13672
                            · linarith only [h13567, h13672, hlam]
                            · linarith only [h0, h13672, hlam]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, h12751, hc01, hc23, hlam, hphi, ht12, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, h13651, hc01, hc23, hlam, hphi, ht12, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          rcases p13659_3 (m.d 0 2) (by simp) with h13679 | h13679
                          · linarith only [h13679, hlam, p13659_0]
                          · rcases p13659_3 (m.d 1 2) (by simp) with h13681 | h13681
                            · linarith only [h13649, h13681, hlam]
                            · linarith only [h0, h13681, hlam]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13655, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, h13651, h13655, hc01, hc23, hlam, hphi, ht12, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          rcases p13659_3 (m.d 0 2) (by simp) with h13688 | h13688
                          · linarith only [h13688, hlam, p13659_0]
                          · rcases p13659_3 (m.d 1 2) (by simp) with h13690 | h13690
                            · linarith only [h13651, h13690, hlam]
                            · linarith only [h0, h13690, hlam]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13656, hlam, p13659_0]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [h13657, hlam, p13659_1]
                        · have p13659_0 := h13659c.1
                          have p13659_1 := h13659c.2.1
                          have p13659_2 := h13659c.2.2.1
                          have p13659_3 := h13659c.2.2.2
                          linarith only [hlam, p13659_0]
                      · rcases h2bigk with h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c | h13697c
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h8886, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h12751, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h13259, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, h13567, hc01, hc23, hlam, hphi, ht12, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h13567, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h13649, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h13651, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          rcases p13697_3 (m.d 0 2) (by simp) with h13708 | h13708
                          · linarith only [h13708, hlam, p13697_0]
                          · rcases p13697_3 (m.d 1 2) (by simp) with h13710 | h13710
                            · linarith only [h13567, h13710, hlam]
                            · linarith only [h0, h13710, hlam]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, h12751, hc01, hc23, hlam, hphi, ht12, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, h13651, hc01, hc23, hlam, hphi, ht12, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          rcases p13697_3 (m.d 0 2) (by simp) with h13717 | h13717
                          · linarith only [h13717, hlam, p13697_0]
                          · rcases p13697_3 (m.d 1 2) (by simp) with h13719 | h13719
                            · linarith only [h13649, h13719, hlam]
                            · linarith only [h0, h13719, hlam]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h13655, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, h13651, h13655, hc01, hc23, hlam, hphi, ht12, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          rcases p13697_3 (m.d 0 2) (by simp) with h13726 | h13726
                          · linarith only [h13726, hlam, p13697_0]
                          · rcases p13697_3 (m.d 1 2) (by simp) with h13728 | h13728
                            · linarith only [h13651, h13728, hlam]
                            · linarith only [h0, h13728, hlam]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h13656, hlam, p13697_0]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [h13657, hlam, p13697_1]
                        · have p13697_0 := h13697c.1
                          have p13697_1 := h13697c.2.1
                          have p13697_2 := h13697c.2.2.1
                          have p13697_3 := h13697c.2.2.2
                          linarith only [hlam, p13697_0]
                    · linarith only [h0, h12751, h13566, h13567, h13653, h13657, h6874, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h13567, h13656, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h13567, h13655, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h13566, h13654, h6874, hlam]
            · linarith only [h0, h13565, h13567, h13653, h8886, hc01, hc23, hlam, hphi, ht12]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13740 | h13740
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13741 | h13741
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13742 | h13742
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13743 | h13743
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13744 | h13744
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13745 | h13745
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13746 | h13746
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13747 | h13747
                    · linarith only [h13566, h13741, h13747, h6874, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12751, h13740, h13743, h13744, h13747, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13750 | h13750
                    · linarith only [h0, h12751, h13566, h13741, h13750, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12751, h13740, h13743, h13744, h13750, hc01, hc12, hlam, hphi]
                · linarith only [h13565, h13745, h8886, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13754 | h13754
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13755 | h13755
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13756 | h13756
                    · linarith only [h13741, h13744, h13756, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13758 | h13758
                      · linarith only [h13565, h13744, h13758, h6874, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h2bigk with h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c | h13760c
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h8886, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h12751, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h13259, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          rcases p13760_3 (m.d 0 2) (by simp) with h13766 | h13766
                          · linarith only [h0, h13766, hlam]
                          · rcases p13760_3 (m.d 1 2) (by simp) with h13768 | h13768
                            · rcases p13760_3 (m.d 2 3) (by simp) with h13769 | h13769
                              · linarith only [h13740, h13769, hlam]
                              · linarith only [h13769, h8886, hlam]
                            · linarith only [h0, h13768, hlam]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h8886, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h12751, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h12751, h13756, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h13740, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h13740, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h12751, h13740, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h12751, h13740, h13756, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h13741, h13744, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h13741, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h13754, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h13756, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h13742, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h13742, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h13755, hlam, p13760_0]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [h0, h12751, h13740, h13755, hc01, hc12, hlam, hphi, p13760_1]
                        · have p13760_0 := h13760c.1
                          have p13760_1 := h13760c.2.1
                          have p13760_2 := h13760c.2.2.1
                          have p13760_3 := h13760c.2.2.2
                          linarith only [hlam, p13760_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13792 | h13792
                    · linarith only [h13744, h13792, h6874, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13794 | h13794
                      · linarith only [h0, h12751, h13565, h13741, h13744, h13794, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h2bigk with h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c | h13796c
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h8886, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h12751, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h13259, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          rcases p13796_3 (m.d 0 2) (by simp) with h13802 | h13802
                          · linarith only [h0, h13802, hlam]
                          · rcases p13796_3 (m.d 1 2) (by simp) with h13804 | h13804
                            · rcases p13796_3 (m.d 2 3) (by simp) with h13805 | h13805
                              · linarith only [h13740, h13805, hlam]
                              · linarith only [h13805, h8886, hlam]
                            · linarith only [h0, h13804, hlam]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h8886, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h12751, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h13259, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h13740, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h13740, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h12751, h13740, h6874, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h13755, hlam, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h13741, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h13741, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h13754, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h13792, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h13742, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h13742, hlam, p13796_0]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h12751, h13742, h13754, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [h0, h12751, h13742, hc01, hc12, hlam, hphi, p13796_1]
                        · have p13796_0 := h13796c.1
                          have p13796_1 := h13796c.2.1
                          have p13796_2 := h13796c.2.2.1
                          have p13796_3 := h13796c.2.2.2
                          linarith only [hlam, p13796_0]
                · linarith only [h13565, h13754, h8886, hlam]
            · linarith only [h13565, h13740, h13743, h8886, hlam]
          · linarith only [h0, h13740, h13742, h8886, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h13740, h13741, h8886, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13832 | h13832
        · linarith only [h0, h12751, h13740, h13832, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13834 | h13834
          · linarith only [h0, h13259, h13740, h13834, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13836 | h13836
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13837 | h13837
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13838 | h13838
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13839 | h13839
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13840 | h13840
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13841 | h13841
                      · linarith only [h13565, h13566, h13841, hlam]
                      · rcases h2bigk with h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c | h13843c
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h8886, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h12751, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h13259, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, h13834, h13838, h13840, hc01, hc23, hlam, hphi, ht12, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h13740, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h13832, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h13834, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          rcases p13843_3 (m.d 0 2) (by simp) with h13854 | h13854
                          · linarith only [h13854, hlam, p13843_0]
                          · rcases p13843_3 (m.d 1 2) (by simp) with h13856 | h13856
                            · linarith only [h13740, h13856, hlam]
                            · linarith only [h0, h13856, hlam]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, h12751, hc01, hc23, hlam, hphi, ht12, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, h13834, hc01, hc23, hlam, hphi, ht12, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          rcases p13843_3 (m.d 0 2) (by simp) with h13863 | h13863
                          · linarith only [h13863, hlam, p13843_0]
                          · rcases p13843_3 (m.d 1 2) (by simp) with h13865 | h13865
                            · linarith only [h13832, h13865, hlam]
                            · linarith only [h0, h13865, hlam]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h13838, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, h13834, h13838, hc01, hc23, hlam, hphi, ht12, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          rcases p13843_3 (m.d 0 2) (by simp) with h13872 | h13872
                          · linarith only [h13872, hlam, p13843_0]
                          · rcases p13843_3 (m.d 1 2) (by simp) with h13874 | h13874
                            · linarith only [h13834, h13874, hlam]
                            · linarith only [h0, h13874, hlam]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h13839, hlam, p13843_0]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [h13840, hlam, p13843_1]
                        · have p13843_0 := h13843c.1
                          have p13843_1 := h13843c.2.1
                          have p13843_2 := h13843c.2.2.1
                          have p13843_3 := h13843c.2.2.2
                          linarith only [hlam, p13843_0]
                    · linarith only [h0, h12751, h13836, h13837, h13840, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h12751, h13566, h13740, h13836, h13837, h13839, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h13565, h13566, h13740, h13836, h13837, h13838, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13884 | h13884
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13885 | h13885
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13886 | h13886
                    · linarith only [h13837, h13884, h13886, h6874, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h13832, h13886, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h13740, h13885, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h13740, h13884, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h13565, h13740, h13836, h8886, hc01, hc23, hlam, hphi, ht12]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13892 | h13892
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13893 | h13893
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13894 | h13894
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13895 | h13895
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13896 | h13896
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13897 | h13897
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13898 | h13898
                · linarith only [h0, h13565, h13893, h13898, h8886, hc01, hc12, hlam, hphi]
                · linarith only [h0, h13896, h13898, h8886, hc01, hc13, hlam, hphi]
              · linarith only [h13892, h13897, h6874, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13902 | h13902
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13903 | h13903
                · linarith only [h13893, h13896, h13903, h6874, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13905 | h13905
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13906 | h13906
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13907 | h13907
                      · rcases h2bigk with h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c | h13908c
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h8886, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h12751, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13259, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          rcases p13908_3 (m.d 0 2) (by simp) with h13914 | h13914
                          · linarith only [h0, h13914, hlam]
                          · rcases p13908_3 (m.d 1 2) (by simp) with h13916 | h13916
                            · rcases p13908_3 (m.d 2 3) (by simp) with h13917 | h13917
                              · linarith only [h13893, h13917, hlam]
                              · linarith only [h13917, h8886, hlam]
                            · linarith only [h0, h13916, hlam]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13259, h13905, hc01, hc12, hlam, hphi, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13259, h13903, h13905, hc01, hc12, hlam, hphi, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13259, hc01, hc12, hlam, hphi, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13893, h13896, hc01, hc34, hlam, hphi, ht12, ht23, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13893, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13903, hlam, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13259, h13893, h13896, hc01, hc34, hlam, hphi, ht12, ht23, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13894, hc01, hc12, hlam, hphi, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13894, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13894, h13905, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13259, h13894, hc01, hc12, hlam, hphi, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h0, h13893, h13905, hc01, hc12, hlam, hphi, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13895, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13905, hlam, p13908_0]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [h13906, hlam, p13908_1]
                        · have p13908_0 := h13908c.1
                          have p13908_1 := h13908c.2.1
                          have p13908_2 := h13908c.2.2.1
                          have p13908_3 := h13908c.2.2.2
                          linarith only [hlam, p13908_0]
                      · linarith only [h0, h13892, h13893, h13896, h13907, h6874, h8886, hc01, hc14, hlam, hphi]
                    · linarith only [h12751, h13892, h13906, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13942 | h13942
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13943 | h13943
                      · rcases h2bigk with h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c | h13944c
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h8886, hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h12751, hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h13259, hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          rcases p13944_3 (m.d 0 2) (by simp) with h13950 | h13950
                          · linarith only [h0, h13950, hlam]
                          · rcases p13944_3 (m.d 1 2) (by simp) with h13952 | h13952
                            · rcases p13944_3 (m.d 2 3) (by simp) with h13953 | h13953
                              · linarith only [h13893, h13953, hlam]
                              · linarith only [h13953, h8886, hlam]
                            · linarith only [h0, h13952, hlam]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h8886, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h12751, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h13905, h8886, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h13905, hc01, hc35, hlam, hphi, ht12, ht23, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h13893, hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h13903, hlam, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h13905, hlam, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h13894, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h13894, hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h13894, h8886, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h13894, h13905, h8886, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h13895, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h13895, hlam, p13944_0]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h0, h13895, h8886, hc01, hc12, hlam, hphi, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [h13942, hlam, p13944_1]
                        · have p13944_0 := h13944c.1
                          have p13944_1 := h13944c.2.1
                          have p13944_2 := h13944c.2.2.1
                          have p13944_3 := h13944c.2.2.2
                          linarith only [hlam, p13944_0]
                      · linarith only [h12751, h13892, h13894, h13896, h13943, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h12751, h13892, h13942, hlam]
              · linarith only [h12751, h13892, h13894, h13902, hlam]
          · linarith only [h0, h12751, h13894, h13895, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h13893, h13894, h8886, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13981 | h13981
        · linarith only [h0, h12751, h13893, h13981, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13983 | h13983
          · linarith only [h0, h13259, h13893, h13983, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13985 | h13985
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13986 | h13986
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13987 | h13987
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13988 | h13988
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13989 | h13989
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13990 | h13990
                      · rcases h2bigk with h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c | h13991c
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h8886, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h12751, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h13259, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, h13983, hc01, hc25, hlam, hphi, ht12, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h13893, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h13981, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h13983, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          rcases p13991_3 (m.d 0 2) (by simp) with h14002 | h14002
                          · linarith only [h14002, hlam, p13991_0]
                          · rcases p13991_3 (m.d 1 2) (by simp) with h14004 | h14004
                            · linarith only [h13893, h14004, hlam]
                            · linarith only [h0, h14004, hlam]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, h12751, hc01, hc23, hlam, hphi, ht12, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, h13983, hc01, hc23, hlam, hphi, ht12, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          rcases p13991_3 (m.d 0 2) (by simp) with h14011 | h14011
                          · linarith only [h14011, hlam, p13991_0]
                          · rcases p13991_3 (m.d 1 2) (by simp) with h14013 | h14013
                            · linarith only [h13981, h14013, hlam]
                            · linarith only [h0, h14013, hlam]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h13987, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, h13983, h13987, hc01, hc23, hlam, hphi, ht12, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          rcases p13991_3 (m.d 0 2) (by simp) with h14020 | h14020
                          · linarith only [h14020, hlam, p13991_0]
                          · rcases p13991_3 (m.d 1 2) (by simp) with h14022 | h14022
                            · linarith only [h13983, h14022, hlam]
                            · linarith only [h0, h14022, hlam]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h13988, hlam, p13991_0]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [h13989, hlam, p13991_1]
                        · have p13991_0 := h13991c.1
                          have p13991_1 := h13991c.2.1
                          have p13991_2 := h13991c.2.2.1
                          have p13991_3 := h13991c.2.2.2
                          linarith only [hlam, p13991_0]
                      · linarith only [h13565, h13892, h13990, hlam]
                    · linarith only [h0, h12751, h13565, h13892, h13893, h13985, h13989, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h13565, h13893, h13985, h13988, h8886, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h13893, h13985, h13987, hlam]
              · linarith only [h13565, h13892, h13985, h13986, h6874, hc01, hc13, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14034 | h14034
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14035 | h14035
                · linarith only [h0, h13893, h13985, h14035, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h13893, h14035, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h13892, h14034, h6874, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14039 | h14039
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14040 | h14040
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14041 | h14041
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14042 | h14042
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14043 | h14043
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14044 | h14044
                · linarith only [h0, h13565, h14039, h14044, h8886, hc01, hc12, hlam, hphi]
                · linarith only [h0, h14042, h14044, h8886, hc01, hc13, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14047 | h14047
                · linarith only [h0, h13565, h14039, h14047, h8886, hc01, hc12, hlam, hphi]
                · linarith only [h0, h14039, h14042, h14047, h8886, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14050 | h14050
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14051 | h14051
                · linarith only [h0, h13565, h14039, h14051, h8886, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14053 | h14053
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14054 | h14054
                    · linarith only [h0, h13565, h13892, h14040, h14054, h8886, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12751, h14050, h14054, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14057 | h14057
                    · linarith only [h0, h13565, h13892, h14040, h14057, h8886, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12751, h14042, h14050, h14057, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14060 | h14060
                · linarith only [h0, h13565, h14039, h14060, h8886, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14062 | h14062
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14063 | h14063
                    · linarith only [h14050, h14063, h6874, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h14060, h14062, h14063, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14066 | h14066
                    · linarith only [h14050, h14066, h6874, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14068 | h14068
                      · linarith only [h0, h14039, h14042, h14050, h14068, h8886, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h14039, h14042, h14068, h8886, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h14039, h14041, h8886, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h14039, h14040, h8886, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14073 | h14073
        · linarith only [h0, h12751, h14039, h14073, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14075 | h14075
          · linarith only [h0, h13259, h14039, h14075, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14077 | h14077
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14078 | h14078
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14079 | h14079
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14080 | h14080
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14081 | h14081
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14082 | h14082
                      · linarith only [h0, h13565, h13892, h14077, h14082, h8886, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h13565, h14078, h14082, h8886, hc01, hc14, hlam, hphi]
                    · linarith only [h14073, h14078, h14081, hlam]
                  · linarith only [h0, h13565, h13892, h14073, h14078, h14079, h14080, h8886, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h13565, h13892, h14039, h14077, h14078, h14079, h8886, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14088 | h14088
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14089 | h14089
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14090 | h14090
                    · linarith only [h14078, h14090, h6874, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h14073, h14090, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h14039, h14089, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h14039, h14077, h14088, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14095 | h14095
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14096 | h14096
                · linarith only [h0, h14039, h14077, h14096, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h14039, h14096, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14099 | h14099
                · linarith only [h0, h14039, h14077, h14099, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h14039, h14099, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 10432000 in
set_option maxHeartbeats 10432000 in
theorem r1l7_12_24_L_I_H_I_s7_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h12751 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  rcases m.htr 0 2 5 (by decide) (by decide) with h13259 | h13259
  · exact r1l7_12_24_L_I_H_I_s7_x1_x1_x0 m hb2 hb4 hg0 hg6874 h8886 h12751 h13259
  · exact r1l7_12_24_L_I_H_I_s7_x1_x1_x1 m hb2 hb4 hg0 hg6874 h8886 h12751 h13259

set_option maxHeartbeats 10432000 in
set_option maxHeartbeats 10432000 in
theorem r1l7_12_24_L_I_H_I_s7_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  rcases m.htr 0 2 4 (by decide) (by decide) with h12751 | h12751
  · exact r1l7_12_24_L_I_H_I_s7_x1_x0 m hb2 hb4 hg0 hg6874 h8886 h12751
  · exact r1l7_12_24_L_I_H_I_s7_x1_x1 m hb2 hb4 hg0 hg6874 h8886 h12751

set_option maxHeartbeats 10432000 in
set_option maxHeartbeats 10432000 in
theorem r1l7_12_24_L_I_H_I_s7 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  rcases m.htr 0 2 3 (by decide) (by decide) with h8886 | h8886
  · exact r1l7_12_24_L_I_H_I_s7_x0 m hb2 hb4 hg0 hg6874 h8886
  · exact r1l7_12_24_L_I_H_I_s7_x1 m hb2 hb4 hg0 hg6874 h8886

end R2N4
