import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S26

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h19120 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h19121 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h19122 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 2 3 5 (by decide) (by decide) with h19721 | h19721
  · rcases m.htr 2 4 5 (by decide) (by decide) with h19722 | h19722
    · rcases m.htr 3 4 5 (by decide) (by decide) with h19723 | h19723
      · rcases h1bigk with h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c | h19724c
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h0, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h14799, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h16563, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h17994, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          rcases p19724_3 (m.d 0 1) (by simp) with h19730 | h19730
          · linarith only [h19730, hlam, p19724_0]
          · rcases p19724_3 (m.d 1 2) (by simp) with h19732 | h19732
            · rcases p19724_3 (m.d 1 3) (by simp) with h19733 | h19733
              · linarith only [h19116, h19733, hlam]
              · linarith only [h14799, h19733, hlam]
            · linarith only [h19732, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h14799, hc01, hc12, hlam, hphi, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h16563, hc01, hc12, hlam, hphi, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          rcases p19724_3 (m.d 0 1) (by simp) with h19741 | h19741
          · linarith only [h19741, hlam, p19724_0]
          · rcases p19724_3 (m.d 1 2) (by simp) with h19743 | h19743
            · rcases p19724_3 (m.d 1 3) (by simp) with h19744 | h19744
              · rcases p19724_3 (m.d 1 4) (by simp) with h19745 | h19745
                · linarith only [h19119, h19745, hlam]
                · linarith only [h16563, h19745, hlam]
              · linarith only [h19744, hlam, p19724_0]
            · linarith only [h0, h19743, hlam]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h19116, hlam, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h16563, hc01, hc13, hlam, hphi, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h17994, h19116, hc01, hc12, hlam, hphi, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          rcases p19724_3 (m.d 0 1) (by simp) with h19754 | h19754
          · linarith only [h19754, hlam, p19724_0]
          · rcases p19724_3 (m.d 1 2) (by simp) with h19756 | h19756
            · rcases p19724_3 (m.d 1 3) (by simp) with h19757 | h19757
              · rcases p19724_3 (m.d 1 4) (by simp) with h19758 | h19758
                · rcases p19724_3 (m.d 1 5) (by simp) with h19759 | h19759
                  · linarith only [h19121, h19759, hlam]
                  · linarith only [h17994, h19759, hlam]
                · linarith only [h19758, hlam, p19724_0]
              · linarith only [h14799, h19757, hlam]
            · linarith only [h0, h19756, hlam]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h19117, hlam, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h19119, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h17994, hc01, hc14, hlam, hphi, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          rcases p19724_3 (m.d 0 1) (by simp) with h19769 | h19769
          · linarith only [h19769, hlam, p19724_0]
          · rcases p19724_3 (m.d 1 2) (by simp) with h19771 | h19771
            · rcases p19724_3 (m.d 1 3) (by simp) with h19772 | h19772
              · rcases p19724_3 (m.d 1 4) (by simp) with h19773 | h19773
                · rcases p19724_3 (m.d 1 5) (by simp) with h19774 | h19774
                  · rcases h3bigk with h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c | h19775c
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h14799, hlam, p19775_1]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      rcases p19775_3 (m.d 0 3) (by simp) with h19778 | h19778
                      · rcases p19775_3 (m.d 1 3) (by simp) with h19779 | h19779
                        · rcases p19775_3 (m.d 2 3) (by simp) with h19780 | h19780
                          · linarith only [h19110, h19780, hlam]
                          · rcases p19775_3 (m.d 3 4) (by simp) with h19782 | h19782
                            · linarith only [h19113, h19782, hlam]
                            · linarith only [h19122, h19782, hlam]
                        · linarith only [h19116, h19779, hlam]
                      · linarith only [h19110, h19778, hlam]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h0, h19110, h19122, h19721, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19775_1]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19113, h19122, h19721, hlam, p19775_2]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19113, h19116, h19122, h19721, h19723, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19775_1]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      rcases p19775_3 (m.d 0 3) (by simp) with h19791 | h19791
                      · linarith only [h14799, h19791, hlam]
                      · linarith only [h19110, h19791, hlam]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19116, h19122, h19721, h19723, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19775_1]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h14799, h19113, h19122, h19721, hlam, p19775_2]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19110, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19116, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19122, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19113, h19122, h19723, hc03, hc45, hlam, hphi, ht0b, ht5b, p19775_1]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19113, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19119, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h0, h19110, h19113, h19721, h19723, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19775_1]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      rcases p19775_3 (m.d 0 3) (by simp) with h19805 | h19805
                      · rcases p19775_3 (m.d 1 3) (by simp) with h19806 | h19806
                        · rcases p19775_3 (m.d 2 3) (by simp) with h19807 | h19807
                          · linarith only [h19122, h19807, hlam]
                          · linarith only [h19721, h19807, hlam]
                        · linarith only [h19120, h19806, hlam]
                      · linarith only [h19114, h19805, hlam]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19114, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19120, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19721, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [h19723, hlam, p19775_0]
                    · have p19775_0 := h19775c.1
                      have p19775_1 := h19775c.2.1
                      have p19775_2 := h19775c.2.2.1
                      have p19775_3 := h19775c.2.2.2
                      linarith only [hlam, p19775_0]
                  · linarith only [h19774, hlam, p19724_0]
                · linarith only [h16563, h19773, hlam]
              · linarith only [h14799, h19772, hlam]
            · linarith only [h0, h19771, hlam]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h19118, hlam, p19724_1]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h19120, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [h19121, hlam, p19724_0]
        · have p19724_0 := h19724c.1
          have p19724_1 := h19724c.2.1
          have p19724_2 := h19724c.2.2.1
          have p19724_3 := h19724c.2.2.2
          linarith only [hlam, p19724_0]
      · linarith only [h0, h19110, h19113, h19115, h19122, h19721, h19723, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
    · linarith only [h19122, h19721, h19722, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h19827 | h19827
    · rcases m.htr 3 4 5 (by decide) (by decide) with h19828 | h19828
      · rcases h1bigk with h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h0, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h14799, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h16563, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h17994, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          rcases p19829_3 (m.d 0 1) (by simp) with h19835 | h19835
          · linarith only [h19835, hlam, p19829_0]
          · rcases p19829_3 (m.d 1 2) (by simp) with h19837 | h19837
            · rcases p19829_3 (m.d 1 3) (by simp) with h19838 | h19838
              · linarith only [h19116, h19838, hlam]
              · linarith only [h14799, h19838, hlam]
            · linarith only [h19837, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h14799, hc01, hc12, hlam, hphi, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h16563, hc01, hc12, hlam, hphi, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          rcases p19829_3 (m.d 0 1) (by simp) with h19846 | h19846
          · linarith only [h19846, hlam, p19829_0]
          · rcases p19829_3 (m.d 1 2) (by simp) with h19848 | h19848
            · rcases p19829_3 (m.d 1 3) (by simp) with h19849 | h19849
              · rcases p19829_3 (m.d 1 4) (by simp) with h19850 | h19850
                · linarith only [h19119, h19850, hlam]
                · linarith only [h16563, h19850, hlam]
              · linarith only [h19849, hlam, p19829_0]
            · linarith only [h0, h19848, hlam]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h19116, hlam, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h17994, h19121, hc01, hc13, hlam, hphi, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h17994, h19116, hc01, hc12, hlam, hphi, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          rcases p19829_3 (m.d 0 1) (by simp) with h19859 | h19859
          · linarith only [h19859, hlam, p19829_0]
          · rcases p19829_3 (m.d 1 2) (by simp) with h19861 | h19861
            · rcases p19829_3 (m.d 1 3) (by simp) with h19862 | h19862
              · rcases p19829_3 (m.d 1 4) (by simp) with h19863 | h19863
                · rcases p19829_3 (m.d 1 5) (by simp) with h19864 | h19864
                  · linarith only [h19121, h19864, hlam]
                  · linarith only [h17994, h19864, hlam]
                · linarith only [h19863, hlam, p19829_0]
              · linarith only [h14799, h19862, hlam]
            · linarith only [h0, h19861, hlam]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h19117, hlam, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h19119, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h17994, hc01, hc14, hlam, hphi, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          rcases p19829_3 (m.d 0 1) (by simp) with h19874 | h19874
          · linarith only [h19874, hlam, p19829_0]
          · rcases p19829_3 (m.d 1 2) (by simp) with h19876 | h19876
            · rcases p19829_3 (m.d 1 3) (by simp) with h19877 | h19877
              · rcases p19829_3 (m.d 1 4) (by simp) with h19878 | h19878
                · rcases p19829_3 (m.d 1 5) (by simp) with h19879 | h19879
                  · rcases h3bigk with h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c | h19880c
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h14799, hlam, p19880_1]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19883 | h19883
                      · rcases p19880_3 (m.d 1 3) (by simp) with h19884 | h19884
                        · rcases p19880_3 (m.d 2 3) (by simp) with h19885 | h19885
                          · linarith only [h19110, h19885, hlam]
                          · rcases p19880_3 (m.d 3 4) (by simp) with h19887 | h19887
                            · linarith only [h19113, h19887, hlam]
                            · linarith only [h19122, h19887, hlam]
                        · linarith only [h19116, h19884, hlam]
                      · linarith only [h19110, h19883, hlam]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19892 | h19892
                      · rcases p19880_3 (m.d 1 3) (by simp) with h19893 | h19893
                        · rcases p19880_3 (m.d 2 3) (by simp) with h19894 | h19894
                          · linarith only [h19110, h19894, hlam]
                          · rcases p19880_3 (m.d 3 4) (by simp) with h19896 | h19896
                            · linarith only [h19896, hlam, p19880_0]
                            · rcases p19880_3 (m.d 3 5) (by simp) with h19898 | h19898
                              · linarith only [h19114, h19898, hlam]
                              · rcases h5bigk with h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c | h19900c
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h17994, hlam, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  rcases p19900_3 (m.d 0 5) (by simp) with h19903 | h19903
                                  · rcases p19900_3 (m.d 1 5) (by simp) with h19904 | h19904
                                    · rcases p19900_3 (m.d 2 5) (by simp) with h19905 | h19905
                                      · linarith only [h19112, h19905, hlam]
                                      · rcases p19900_3 (m.d 3 5) (by simp) with h19907 | h19907
                                        · linarith only [h19114, h19907, hlam]
                                        · linarith only [h19721, h19907, hlam]
                                    · linarith only [h19118, h19904, hlam]
                                  · linarith only [h19112, h19903, hlam]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19113, h19115, h19721, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  rcases p19900_3 (m.d 0 5) (by simp) with h19913 | h19913
                                  · rcases p19900_3 (m.d 1 5) (by simp) with h19914 | h19914
                                    · rcases p19900_3 (m.d 2 5) (by simp) with h19915 | h19915
                                      · linarith only [h19112, h19915, hlam]
                                      · linarith only [h19827, h19915, hlam]
                                    · linarith only [h19121, h19914, hlam]
                                  · linarith only [h19115, h19913, hlam]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h17994, hc01, hc15, hlam, hphi, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  rcases p19900_3 (m.d 0 5) (by simp) with h19922 | h19922
                                  · linarith only [h17994, h19922, hlam]
                                  · linarith only [h19112, h19922, hlam]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19116, h19119, h19121, h19721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  rcases p19900_3 (m.d 0 5) (by simp) with h19926 | h19926
                                  · linarith only [h17994, h19926, hlam]
                                  · linarith only [h19115, h19926, hlam]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19112, hlam, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19118, hlam, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19721, hlam, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h0, h19112, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19114, hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19120, hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h14799, h19116, h19828, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19880_1, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h14799, h19116, h19828, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19880_1, p19900_1]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19115, hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19121, hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19827, hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [h19828, hlam, p19900_0]
                                · have p19900_0 := h19900c.1
                                  have p19900_1 := h19900c.2.1
                                  have p19900_2 := h19900c.2.2.1
                                  have p19900_3 := h19900c.2.2.2
                                  linarith only [hlam, p19900_0]
                        · linarith only [h19119, h19893, hlam]
                      · linarith only [h19892, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19946 | h19946
                      · rcases p19880_3 (m.d 1 3) (by simp) with h19947 | h19947
                        · rcases p19880_3 (m.d 2 3) (by simp) with h19948 | h19948
                          · linarith only [h19110, h19948, hlam]
                          · rcases p19880_3 (m.d 3 4) (by simp) with h19950 | h19950
                            · linarith only [h19113, h19950, hlam]
                            · linarith only [h19828, h19950, hlam]
                        · linarith only [h19120, h19947, hlam]
                      · linarith only [h19946, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19113, h19116, h19122, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19880_1]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19957 | h19957
                      · linarith only [h14799, h19957, hlam]
                      · linarith only [h19110, h19957, hlam]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19960 | h19960
                      · linarith only [h14799, h19960, hlam]
                      · linarith only [h19113, h19960, hlam]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19963 | h19963
                      · linarith only [h14799, h19963, hlam]
                      · linarith only [h19114, h19963, hlam]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19110, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19116, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19122, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19721, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19113, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19119, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19973 | h19973
                      · rcases p19880_3 (m.d 1 3) (by simp) with h19974 | h19974
                        · rcases p19880_3 (m.d 2 3) (by simp) with h19975 | h19975
                          · linarith only [h19975, hlam, p19880_0]
                          · rcases p19880_3 (m.d 3 4) (by simp) with h19977 | h19977
                            · rcases p19880_3 (m.d 3 5) (by simp) with h19978 | h19978
                              · linarith only [h19828, h19978, hlam]
                              · linarith only [h19721, h19978, hlam]
                            · linarith only [h19977, hlam, p19880_0]
                        · linarith only [h19116, h19974, hlam]
                      · linarith only [h19110, h19973, hlam]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19113, h19721, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19880_1]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19114, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19120, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      rcases p19880_3 (m.d 0 3) (by simp) with h19988 | h19988
                      · rcases p19880_3 (m.d 1 3) (by simp) with h19989 | h19989
                        · rcases p19880_3 (m.d 2 3) (by simp) with h19990 | h19990
                          · linarith only [h19990, hlam, p19880_0]
                          · rcases p19880_3 (m.d 3 4) (by simp) with h19992 | h19992
                            · rcases p19880_3 (m.d 3 5) (by simp) with h19993 | h19993
                              · rcases h5bigk with h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c | h19994c
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h17994, hlam, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  rcases p19994_3 (m.d 0 5) (by simp) with h19997 | h19997
                                  · rcases p19994_3 (m.d 1 5) (by simp) with h19998 | h19998
                                    · rcases p19994_3 (m.d 2 5) (by simp) with h19999 | h19999
                                      · linarith only [h19112, h19999, hlam]
                                      · rcases p19994_3 (m.d 3 5) (by simp) with h20001 | h20001
                                        · linarith only [h19114, h20001, hlam]
                                        · linarith only [h19721, h20001, hlam]
                                    · linarith only [h19118, h19998, hlam]
                                  · linarith only [h19112, h19997, hlam]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19880_1, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  rcases p19994_3 (m.d 0 5) (by simp) with h20007 | h20007
                                  · rcases p19994_3 (m.d 1 5) (by simp) with h20008 | h20008
                                    · rcases p19994_3 (m.d 2 5) (by simp) with h20009 | h20009
                                      · linarith only [h19112, h20009, hlam]
                                      · linarith only [h19827, h20009, hlam]
                                    · linarith only [h19121, h20008, hlam]
                                  · linarith only [h19115, h20007, hlam]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h17994, h19116, h19119, h19121, hc01, hc12, hlam, hphi, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  rcases p19994_3 (m.d 0 5) (by simp) with h20016 | h20016
                                  · linarith only [h17994, h20016, hlam]
                                  · linarith only [h19112, h20016, hlam]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19116, h19119, h19121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19880_1, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  rcases p19994_3 (m.d 0 5) (by simp) with h20020 | h20020
                                  · linarith only [h17994, h20020, hlam]
                                  · linarith only [h19115, h20020, hlam]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19112, hlam, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19118, hlam, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19721, hlam, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h0, h19112, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19114, hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19120, hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h14799, h19114, h19116, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h14799, h19113, h19116, h19828, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19994_1]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19115, hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19121, hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19827, hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [h19828, hlam, p19994_0]
                                · have p19994_0 := h19994c.1
                                  have p19994_1 := h19994c.2.1
                                  have p19994_2 := h19994c.2.2.1
                                  have p19994_3 := h19994c.2.2.2
                                  linarith only [hlam, p19994_0]
                              · linarith only [h19993, hlam, p19880_0]
                            · linarith only [h19122, h19992, hlam]
                        · linarith only [h19116, h19989, hlam]
                      · linarith only [h19110, h19988, hlam]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [h19828, hlam, p19880_0]
                    · have p19880_0 := h19880c.1
                      have p19880_1 := h19880c.2.1
                      have p19880_2 := h19880c.2.2.1
                      have p19880_3 := h19880c.2.2.2
                      linarith only [hlam, p19880_0]
                  · linarith only [h19879, hlam, p19829_0]
                · linarith only [h16563, h19878, hlam]
              · linarith only [h14799, h19877, hlam]
            · linarith only [h0, h19876, hlam]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h19118, hlam, p19829_1]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h19120, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [h19121, hlam, p19829_0]
        · have p19829_0 := h19829c.1
          have p19829_1 := h19829c.2.1
          have p19829_2 := h19829c.2.2.1
          have p19829_3 := h19829c.2.2.2
          linarith only [hlam, p19829_0]
      · linarith only [h0, h19111, h19122, h19827, h19828, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h20053 | h20053
      · rcases h1bigk with h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c | h20054c
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h0, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h14799, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h16563, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h17994, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          rcases p20054_3 (m.d 0 1) (by simp) with h20060 | h20060
          · linarith only [h20060, hlam, p20054_0]
          · rcases p20054_3 (m.d 1 2) (by simp) with h20062 | h20062
            · rcases p20054_3 (m.d 1 3) (by simp) with h20063 | h20063
              · linarith only [h19116, h20063, hlam]
              · linarith only [h14799, h20063, hlam]
            · linarith only [h20062, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h14799, h19113, h19827, h20053, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h16563, hc01, hc12, hlam, hphi, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          rcases p20054_3 (m.d 0 1) (by simp) with h20071 | h20071
          · linarith only [h20071, hlam, p20054_0]
          · rcases p20054_3 (m.d 1 2) (by simp) with h20073 | h20073
            · rcases p20054_3 (m.d 1 3) (by simp) with h20074 | h20074
              · rcases p20054_3 (m.d 1 4) (by simp) with h20075 | h20075
                · linarith only [h19119, h20075, hlam]
                · linarith only [h16563, h20075, hlam]
              · linarith only [h20074, hlam, p20054_0]
            · linarith only [h0, h20073, hlam]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h19116, hlam, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h16563, h19113, h19122, h19827, h20053, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h17994, h19116, hc01, hc12, hlam, hphi, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          rcases p20054_3 (m.d 0 1) (by simp) with h20084 | h20084
          · linarith only [h20084, hlam, p20054_0]
          · rcases p20054_3 (m.d 1 2) (by simp) with h20086 | h20086
            · rcases p20054_3 (m.d 1 3) (by simp) with h20087 | h20087
              · rcases p20054_3 (m.d 1 4) (by simp) with h20088 | h20088
                · rcases p20054_3 (m.d 1 5) (by simp) with h20089 | h20089
                  · linarith only [h19121, h20089, hlam]
                  · linarith only [h17994, h20089, hlam]
                · linarith only [h20088, hlam, p20054_0]
              · linarith only [h14799, h20087, hlam]
            · linarith only [h0, h20086, hlam]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h19117, hlam, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h19119, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h17994, hc01, hc14, hlam, hphi, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          rcases p20054_3 (m.d 0 1) (by simp) with h20099 | h20099
          · linarith only [h20099, hlam, p20054_0]
          · rcases p20054_3 (m.d 1 2) (by simp) with h20101 | h20101
            · rcases p20054_3 (m.d 1 3) (by simp) with h20102 | h20102
              · rcases p20054_3 (m.d 1 4) (by simp) with h20103 | h20103
                · rcases p20054_3 (m.d 1 5) (by simp) with h20104 | h20104
                  · rcases h3bigk with h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c | h20105c
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h14799, hlam, p20105_1]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19113, h19122, h19827, h20053, hlam, p20105_2]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19122, h19827, h20053, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20105_1]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      rcases p20105_3 (m.d 0 3) (by simp) with h20110 | h20110
                      · rcases p20105_3 (m.d 1 3) (by simp) with h20111 | h20111
                        · rcases p20105_3 (m.d 2 3) (by simp) with h20112 | h20112
                          · linarith only [h19110, h20112, hlam]
                          · rcases p20105_3 (m.d 3 4) (by simp) with h20114 | h20114
                            · linarith only [h19113, h20114, hlam]
                            · linarith only [h20053, h20114, hlam]
                        · linarith only [h19120, h20111, hlam]
                      · linarith only [h20110, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19113, h19116, h19122, h19827, h20053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20105_1]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h14799, h19113, h19122, h19827, h20053, hlam, p20105_2]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19122, h19827, h20053, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20105_1]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      rcases p20105_3 (m.d 0 3) (by simp) with h20123 | h20123
                      · linarith only [h14799, h20123, hlam]
                      · linarith only [h19114, h20123, hlam]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19110, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19116, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19122, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19721, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19113, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19119, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      rcases p20105_3 (m.d 0 3) (by simp) with h20133 | h20133
                      · rcases p20105_3 (m.d 1 3) (by simp) with h20134 | h20134
                        · rcases p20105_3 (m.d 2 3) (by simp) with h20135 | h20135
                          · linarith only [h20135, hlam, p20105_0]
                          · rcases p20105_3 (m.d 3 4) (by simp) with h20137 | h20137
                            · rcases p20105_3 (m.d 3 5) (by simp) with h20138 | h20138
                              · linarith only [h20053, h20138, hlam]
                              · linarith only [h19721, h20138, hlam]
                            · linarith only [h20137, hlam, p20105_0]
                        · linarith only [h19116, h20134, hlam]
                      · linarith only [h19110, h20133, hlam]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19113, h19122, h19827, h20053, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20105_1]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19114, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h19120, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      rcases p20105_3 (m.d 0 3) (by simp) with h20148 | h20148
                      · rcases p20105_3 (m.d 1 3) (by simp) with h20149 | h20149
                        · rcases p20105_3 (m.d 2 3) (by simp) with h20150 | h20150
                          · linarith only [h20150, hlam, p20105_0]
                          · rcases p20105_3 (m.d 3 4) (by simp) with h20152 | h20152
                            · rcases p20105_3 (m.d 3 5) (by simp) with h20153 | h20153
                              · rcases h5bigk with h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c | h20154c
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h17994, hlam, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  rcases p20154_3 (m.d 0 5) (by simp) with h20157 | h20157
                                  · rcases p20154_3 (m.d 1 5) (by simp) with h20158 | h20158
                                    · rcases p20154_3 (m.d 2 5) (by simp) with h20159 | h20159
                                      · linarith only [h19112, h20159, hlam]
                                      · rcases p20154_3 (m.d 3 5) (by simp) with h20161 | h20161
                                        · linarith only [h19114, h20161, hlam]
                                        · linarith only [h19721, h20161, hlam]
                                    · linarith only [h19118, h20158, hlam]
                                  · linarith only [h19112, h20157, hlam]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19115, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20105_1, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h16563, h19115, h19116, h19119, h19122, h19827, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h17994, hc01, hc15, hlam, hphi, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  rcases p20154_3 (m.d 0 5) (by simp) with h20170 | h20170
                                  · linarith only [h17994, h20170, hlam]
                                  · linarith only [h19112, h20170, hlam]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19116, h19119, h19121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20105_1, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19116, h19119, h19121, h19122, h19827, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19112, hlam, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19118, hlam, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19721, hlam, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19827, hlam, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19114, hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19120, hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19122, h19827, hc23, hc35, hlam, hphi, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h14799, h19113, h19116, h19122, h19827, h20053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19115, hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19121, hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h19122, h19827, hc23, hc45, hlam, hphi, ht34, p20154_1]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [h20053, hlam, p20154_0]
                                · have p20154_0 := h20154c.1
                                  have p20154_1 := h20154c.2.1
                                  have p20154_2 := h20154c.2.2.1
                                  have p20154_3 := h20154c.2.2.2
                                  linarith only [hlam, p20154_0]
                              · linarith only [h20153, hlam, p20105_0]
                            · linarith only [h19122, h20152, hlam]
                        · linarith only [h19116, h20149, hlam]
                      · linarith only [h19110, h20148, hlam]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [h20053, hlam, p20105_0]
                    · have p20105_0 := h20105c.1
                      have p20105_1 := h20105c.2.1
                      have p20105_2 := h20105c.2.2.1
                      have p20105_3 := h20105c.2.2.2
                      linarith only [hlam, p20105_0]
                  · linarith only [h20104, hlam, p20054_0]
                · linarith only [h16563, h20103, hlam]
              · linarith only [h14799, h20102, hlam]
            · linarith only [h0, h20101, hlam]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h19118, hlam, p20054_1]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h19120, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [h19121, hlam, p20054_0]
        · have p20054_0 := h20054c.1
          have p20054_1 := h20054c.2.1
          have p20054_2 := h20054c.2.2.1
          have p20054_3 := h20054c.2.2.2
          linarith only [hlam, p20054_0]
      · rcases h1bigk with h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c | h20204c
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h0, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h14799, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h16563, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h17994, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          rcases p20204_3 (m.d 0 1) (by simp) with h20210 | h20210
          · linarith only [h20210, hlam, p20204_0]
          · rcases p20204_3 (m.d 1 2) (by simp) with h20212 | h20212
            · rcases p20204_3 (m.d 1 3) (by simp) with h20213 | h20213
              · linarith only [h19116, h20213, hlam]
              · linarith only [h14799, h20213, hlam]
            · linarith only [h20212, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h16563, h19115, h19119, h20053, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h16563, h19115, h20053, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h17994, hc01, hc12, hlam, hphi, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          rcases p20204_3 (m.d 0 1) (by simp) with h20221 | h20221
          · linarith only [h20221, hlam, p20204_0]
          · rcases p20204_3 (m.d 1 2) (by simp) with h20223 | h20223
            · rcases p20204_3 (m.d 1 3) (by simp) with h20224 | h20224
              · rcases p20204_3 (m.d 1 4) (by simp) with h20225 | h20225
                · linarith only [h19119, h20225, hlam]
                · linarith only [h16563, h20225, hlam]
              · linarith only [h20224, hlam, p20204_0]
            · linarith only [h0, h20223, hlam]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h19116, hlam, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h16563, h19115, h19122, h20053, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h17994, h19115, h19116, h19122, h20053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          rcases p20204_3 (m.d 0 1) (by simp) with h20234 | h20234
          · linarith only [h20234, hlam, p20204_0]
          · rcases p20204_3 (m.d 1 2) (by simp) with h20236 | h20236
            · rcases p20204_3 (m.d 1 3) (by simp) with h20237 | h20237
              · rcases p20204_3 (m.d 1 4) (by simp) with h20238 | h20238
                · rcases p20204_3 (m.d 1 5) (by simp) with h20239 | h20239
                  · linarith only [h19121, h20239, hlam]
                  · linarith only [h17994, h20239, hlam]
                · linarith only [h20238, hlam, p20204_0]
              · linarith only [h14799, h20237, hlam]
            · linarith only [h0, h20236, hlam]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h19117, hlam, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h19119, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h17994, h19115, h19122, h20053, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          rcases p20204_3 (m.d 0 1) (by simp) with h20249 | h20249
          · linarith only [h20249, hlam, p20204_0]
          · rcases p20204_3 (m.d 1 2) (by simp) with h20251 | h20251
            · rcases p20204_3 (m.d 1 3) (by simp) with h20252 | h20252
              · rcases p20204_3 (m.d 1 4) (by simp) with h20253 | h20253
                · rcases p20204_3 (m.d 1 5) (by simp) with h20254 | h20254
                  · rcases h3bigk with h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c | h20255c
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h14799, hlam, p20255_1]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19113, h19115, h19122, h20053, hlam, p20255_2]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      rcases p20255_3 (m.d 0 3) (by simp) with h20259 | h20259
                      · rcases p20255_3 (m.d 1 3) (by simp) with h20260 | h20260
                        · rcases p20255_3 (m.d 2 3) (by simp) with h20261 | h20261
                          · linarith only [h19110, h20261, hlam]
                          · rcases p20255_3 (m.d 3 4) (by simp) with h20263 | h20263
                            · linarith only [h20263, hlam, p20255_0]
                            · rcases p20255_3 (m.d 3 5) (by simp) with h20265 | h20265
                              · linarith only [h19114, h20265, hlam]
                              · linarith only [h20053, h20265, hlam]
                        · linarith only [h19119, h20260, hlam]
                      · linarith only [h20259, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      rcases p20255_3 (m.d 0 3) (by simp) with h20270 | h20270
                      · rcases p20255_3 (m.d 1 3) (by simp) with h20271 | h20271
                        · rcases p20255_3 (m.d 2 3) (by simp) with h20272 | h20272
                          · linarith only [h19110, h20272, hlam]
                          · rcases p20255_3 (m.d 3 4) (by simp) with h20274 | h20274
                            · linarith only [h19113, h20274, hlam]
                            · rcases p20255_3 (m.d 3 5) (by simp) with h20276 | h20276
                              · linarith only [h20276, hlam, p20255_0]
                              · rcases h5bigk with h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c | h20278c
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h17994, hlam, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  rcases p20278_3 (m.d 0 5) (by simp) with h20281 | h20281
                                  · rcases p20278_3 (m.d 1 5) (by simp) with h20282 | h20282
                                    · rcases p20278_3 (m.d 2 5) (by simp) with h20283 | h20283
                                      · linarith only [h19112, h20283, hlam]
                                      · rcases p20278_3 (m.d 3 5) (by simp) with h20285 | h20285
                                        · linarith only [h19114, h20285, hlam]
                                        · linarith only [h19721, h20285, hlam]
                                    · linarith only [h19118, h20282, hlam]
                                  · linarith only [h19112, h20281, hlam]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19113, h19115, hlam, p20255_2, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19113, h19115, h19122, h20053, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h17994, hc01, hc15, hlam, hphi, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  rcases p20278_3 (m.d 0 5) (by simp) with h20294 | h20294
                                  · linarith only [h17994, h20294, hlam]
                                  · linarith only [h19112, h20294, hlam]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19116, h19119, h19121, h19122, h20053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19116, h19119, h19121, h19122, h20053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19112, hlam, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19118, hlam, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19721, hlam, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19827, hlam, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19114, hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19120, hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19122, h19827, hc23, hc35, hlam, hphi, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h20053, hlam, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19115, hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19121, hlam, p20278_0]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h19122, h19827, hc23, hc45, hlam, hphi, ht34, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [h14799, h19113, h19115, h19116, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p20278_1]
                                · have p20278_0 := h20278c.1
                                  have p20278_1 := h20278c.2.1
                                  have p20278_2 := h20278c.2.2.1
                                  have p20278_3 := h20278c.2.2.2
                                  linarith only [hlam, p20278_0]
                        · linarith only [h19120, h20271, hlam]
                      · linarith only [h20270, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19113, h19116, h19122, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20255_1]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h14799, h19113, h19115, h19122, h20053, hlam, p20255_2]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      rcases p20255_3 (m.d 0 3) (by simp) with h20319 | h20319
                      · linarith only [h14799, h20319, hlam]
                      · linarith only [h19113, h20319, hlam]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      rcases p20255_3 (m.d 0 3) (by simp) with h20322 | h20322
                      · linarith only [h14799, h20322, hlam]
                      · linarith only [h19114, h20322, hlam]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19110, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19116, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19122, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19721, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19113, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19119, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19113, h19115, h20053, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p20255_1]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h20053, hlam, p20255_1]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19114, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19120, hlam, p20255_0]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      rcases p20255_3 (m.d 0 3) (by simp) with h20337 | h20337
                      · rcases p20255_3 (m.d 1 3) (by simp) with h20338 | h20338
                        · rcases p20255_3 (m.d 2 3) (by simp) with h20339 | h20339
                          · linarith only [h20339, hlam, p20255_0]
                          · rcases p20255_3 (m.d 3 4) (by simp) with h20341 | h20341
                            · linarith only [h20053, h20341, hlam]
                            · linarith only [h19122, h20341, hlam]
                        · linarith only [h19116, h20338, hlam]
                      · linarith only [h19110, h20337, hlam]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [h19122, hc23, hc35, hlam, hphi, p20255_1]
                    · have p20255_0 := h20255c.1
                      have p20255_1 := h20255c.2.1
                      have p20255_2 := h20255c.2.2.1
                      have p20255_3 := h20255c.2.2.2
                      linarith only [hlam, p20255_0]
                  · linarith only [h20254, hlam, p20204_0]
                · linarith only [h16563, h20253, hlam]
              · linarith only [h14799, h20252, hlam]
            · linarith only [h0, h20251, hlam]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h19118, hlam, p20204_1]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h19120, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [h19121, hlam, p20204_0]
        · have p20204_0 := h20204c.1
          have p20204_1 := h20204c.2.1
          have p20204_2 := h20204c.2.2.1
          have p20204_3 := h20204c.2.2.2
          linarith only [hlam, p20204_0]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h19120 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h19121 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 2 3 4 (by decide) (by decide) with h19122 | h19122
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119 h19120 h19121 h19122
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119 h19120 h19121 h19122

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h19120 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h19121 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  linarith only [h0, h16563, h19110, h19113, h19115, h19121, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h19120 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 1 4 5 (by decide) (by decide) with h19121 | h19121
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119 h19120 h19121
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119 h19120 h19121

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h19120 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  linarith only [h14799, h19114, h19120, hlam]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 1 3 5 (by decide) (by decide) with h19120 | h19120
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119 h19120
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119 h19120

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h19119 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  linarith only [h14799, h19113, h19119, hlam]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 1 3 4 (by decide) (by decide) with h19119 | h19119
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113 h19114 h19115 h19116 h19117 h19118 h19119

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h19114 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h19115 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h19116 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h19117 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h19118 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  linarith only [h0, h19112, h19118, hlam]

end R2N4
