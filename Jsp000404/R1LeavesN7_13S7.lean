import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S4
import Jsp000404.R1LeavesN7_13S5
import Jsp000404.R1LeavesN7_13S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2669 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2986 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3195 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h3695 | h3695
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3696 | h3696
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3697 | h3697
      · linarith only [h0, h3697, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3699 | h3699
        · linarith only [h1, h2669, h3195, h3697, h3699, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3701 | h3701
          · linarith only [h0, h2986, h3701, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3703 | h3703
            · linarith only [h1, h3195, h3703, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3705 | h3705
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3706 | h3706
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3707 | h3707
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3708 | h3708
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3709 | h3709
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3710 | h3710
                        · rcases h2bigk with h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c | h3711c
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h2986, hc12, hc25, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h4, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h2669, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h2986, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h0, hlam, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h3697, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h3699, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h3701, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h3707, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h0, h2986, h3707, hc12, hc23, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h3708, hlam, p3711_0]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [h3709, hlam, p3711_1]
                          · have p3711_0 := h3711c.1
                            have p3711_1 := h3711c.2.1
                            have p3711_2 := h3711c.2.2.1
                            have p3711_3 := h3711c.2.2.2
                            linarith only [hlam, p3711_0]
                        · linarith only [h3195, h3696, h3710, hlam]
                      · linarith only [h0, h2, h2669, h3706, h3709, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h2, h3195, h3705, h3707, h3708, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3740 | h3740
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3741 | h3741
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3742 | h3742
                        · rcases h2bigk with h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3707, h4, hc12, hc34, hlam, hphi, ht23, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h4, hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h2669, hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h2986, hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h0, hlam, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3697, hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3699, hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3701, hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3707, hc02, hc34, hlam, hphi, ht23, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3707, hc12, hc34, hlam, hphi, ht23, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3707, hlam, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3707, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3707, h4, hc03, hc34, hlam, hphi, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h0, h2986, h3707, hc12, hc34, hlam, hphi, ht23, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h0, h3740, hc12, hc23, hlam, hphi, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3740, hc12, hc23, hlam, hphi, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3740, hlam, p3743_0]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [h3741, hlam, p3743_1]
                          · have p3743_0 := h3743c.1
                            have p3743_1 := h3743c.2.1
                            have p3743_2 := h3743c.2.2.1
                            have p3743_3 := h3743c.2.2.2
                            linarith only [hlam, p3743_0]
                        · linarith only [h0, h3707, h3742, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h2, h2669, h3706, h3741, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h3705, h3740, h4, hlam]
                · linarith only [h3703, h3705, h3706, hlam]
              · linarith only [h3195, h3695, h3705, hc13, hc34, hlam, hphi]
    · linarith only [h3195, h3695, h3696, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3775 | h3775
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3776 | h3776
      · linarith only [h0, h3776, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3778 | h3778
        · linarith only [h0, h2669, h3778, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3780 | h3780
          · linarith only [h0, h2986, h3780, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3782 | h3782
            · linarith only [h1, h3195, h3782, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3784 | h3784
              · linarith only [h1, h3695, h3784, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3786 | h3786
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3787 | h3787
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3788 | h3788
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3789 | h3789
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3790 | h3790
                        · rcases h2bigk with h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c | h3791c
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h4, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h2669, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h2986, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h0, hlam, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h3776, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h3778, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h3780, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h3695, h3788, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h3787, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h0, h3695, h3787, h3788, h4, hc12, hc23, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h3788, hlam, p3791_0]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [h3789, hlam, p3791_1]
                          · have p3791_0 := h3791c.1
                            have p3791_1 := h3791c.2.1
                            have p3791_2 := h3791c.2.2.1
                            have p3791_3 := h3791c.2.2.2
                            linarith only [hlam, p3791_0]
                        · linarith only [h0, h2, h3195, h3786, h3790, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h2669, h3775, h3789, hlam]
                    · linarith only [h0, h3195, h3787, h3788, h4, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3820 | h3820
                    · linarith only [h0, h3695, h3787, h3820, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3822 | h3822
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3823 | h3823
                        · rcases h2bigk with h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c | h3824c
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3820, h3823, h4, hc12, hc34, hlam, hphi, ht23, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h4, hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h2669, hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h2986, hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h0, hlam, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3776, hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3778, hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3780, hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3820, h3823, hc02, hc34, hlam, hphi, ht23, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3820, h3823, hc12, hc34, hlam, hphi, ht23, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3787, hlam, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3820, hlam, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h0, h3787, hc12, hc34, hlam, hphi, ht23, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3787, hc12, hc34, hlam, hphi, ht23, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3787, hc23, hc34, hlam, hphi, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [hlam, p3824_0]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h0, h2986, h3787, hc12, hc34, hlam, hphi, ht23, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h0, h3820, h3823, h4, hc12, hc34, hlam, hphi, ht23, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [h3822, hlam, p3824_1]
                          · have p3824_0 := h3824c.1
                            have p3824_1 := h3824c.2.1
                            have p3824_2 := h3824c.2.2.1
                            have p3824_3 := h3824c.2.2.2
                            linarith only [hlam, p3824_0]
                        · linarith only [h2, h2669, h3786, h3787, h3823, hlam]
                      · linarith only [h2, h2669, h3786, h3822, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3852 | h3852
                  · linarith only [h3195, h3775, h3776, h3782, h3786, h3852, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3854 | h3854
                    · linarith only [h0, h3695, h3852, h3854, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3856 | h3856
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3857 | h3857
                        · rcases h2bigk with h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c | h3858c
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3854, h3857, h4, hc12, hc34, hlam, hphi, ht23, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h4, hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h2669, hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h2986, hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h0, hlam, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3776, hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3778, hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3780, hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3854, h3857, hc02, hc34, hlam, hphi, ht23, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3854, h3857, hc12, hc34, hlam, hphi, ht23, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3852, hlam, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3854, hlam, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3852, hc23, hc34, hlam, hphi, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [hlam, p3858_0]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h2986, h3775, h3776, h3782, h3786, h3852, hc12, hc34, hlam, hphi, ht23, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h0, h3854, h3857, h4, hc12, hc34, hlam, hphi, ht23, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [h3856, hlam, p3858_1]
                          · have p3858_0 := h3858c.1
                            have p3858_1 := h3858c.2.1
                            have p3858_2 := h3858c.2.2.1
                            have p3858_3 := h3858c.2.2.2
                            linarith only [hlam, p3858_0]
                        · linarith only [h2669, h3775, h3852, h3857, hlam]
                      · linarith only [h2669, h3775, h3856, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3886 | h3886
      · linarith only [h0, h3886, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3888 | h3888
        · linarith only [h0, h2669, h3888, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3890 | h3890
          · linarith only [h0, h2986, h3890, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3892 | h3892
            · linarith only [h1, h3195, h3892, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3894 | h3894
              · linarith only [h1, h3695, h3894, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3896 | h3896
                · linarith only [h2, h3775, h3896, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3898 | h3898
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3899 | h3899
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3900 | h3900
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3901 | h3901
                        · linarith only [h0, h3195, h3775, h3898, h3901, h4, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h3195, h3900, h3901, h4, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3904 | h3904
                        · linarith only [h0, h2669, h3900, h3904, hc12, hc34, hlam, hphi, ht23]
                        · rcases h2bigk with h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c | h3906c
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3195, h3898, h4, hc12, hc24, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h4, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h2669, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h2986, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h0, hlam, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3886, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3888, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3890, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h0, h2669, hc12, hc23, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h0, h2986, hc12, hc23, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h0, hc12, hc24, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hc12, hc24, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3898, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3900, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3899, hlam, p3906_0]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [h3900, hc24, hc45, hlam, hphi, p3906_1]
                          · have p3906_0 := h3906c.1
                            have p3906_1 := h3906c.2.1
                            have p3906_2 := h3906c.2.2.1
                            have p3906_3 := h3906c.2.2.2
                            linarith only [hlam, p3906_0]
                    · linarith only [h0, h3195, h3898, h3899, h4, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3933 | h3933
                    · linarith only [h0, h3695, h3898, h3933, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3935 | h3935
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3936 | h3936
                        · rcases h2bigk with h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h4, hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h2669, hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h2986, hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h0, hlam, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3886, hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3888, hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3890, hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3933, hc12, hc35, hlam, hphi, ht23, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3898, hlam, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3933, hlam, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h0, h3898, hc12, hc34, hlam, hphi, ht23, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3898, hc12, hc34, hlam, hphi, ht23, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3898, hc23, hc34, hlam, hphi, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [hlam, p3937_0]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h0, h2986, h3898, hc12, hc34, hlam, hphi, ht23, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h0, hc12, hc25, hlam, hphi, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [hc12, hc25, hlam, hphi, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h0, h3933, h4, hc12, hc35, hlam, hphi, ht23, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [h3935, hlam, p3937_1]
                          · have p3937_0 := h3937c.1
                            have p3937_1 := h3937c.2.1
                            have p3937_2 := h3937c.2.2.1
                            have p3937_3 := h3937c.2.2.2
                            linarith only [hlam, p3937_0]
                        · linarith only [h3898, h3935, h3936, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3964 | h3964
                        · linarith only [h0, h2669, h3935, h3964, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h3898, h3964, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2669 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2986 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h3195 | h3195
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x1_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2669 h2986 h3195
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x1_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2669 h2986 h3195

set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2669 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h2986 | h2986
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2669 h2986
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2669 h2986

set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h2669 | h2669
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2669
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x1_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2669

set_option maxHeartbeats 7926000 in
set_option maxHeartbeats 7926000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s3 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x0 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3_x1 m hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 8174000 in
set_option maxHeartbeats 8174000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s2 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_22_13_15_H_I_L_I_L_I_s3 m hb2 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3967 | h3967
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3968 | h3968
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3969 | h3969
        · linarith only [h0, h3, h3969, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3971 | h3971
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3972 | h3972
            · linarith only [h1, h3, h3972, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3974 | h3974
              · linarith only [h2, h3, h3974, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3976 | h3976
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3977 | h3977
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3978 | h3978
                    · linarith only [h0, h3969, h3978, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3980 | h3980
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3981 | h3981
                        · linarith only [h1, h3, h3972, h3978, h3981, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h3976, h3981, hc23, hc35, hlam, hphi]
                      · linarith only [h3971, h3972, h3980, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h3, h3968, h3976, h3977, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h3967, h3969, h3976, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3987 | h3987
            · linarith only [h1, h3, h3987, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3989 | h3989
              · linarith only [h0, h3, h3968, h3989, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3991 | h3991
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3992 | h3992
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3993 | h3993
                    · linarith only [h0, h3969, h3993, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3995 | h3995
                      · linarith only [h1, h3971, h3995, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3997 | h3997
                        · linarith only [h0, h1, h3, h3971, h3987, h3991, h3997, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h3, h3991, h3997, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h3968, h3991, h3992, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h3967, h3969, h3991, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4002 | h4002
        · linarith only [h2, h3, h3968, h4002, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4004 | h4004
          · linarith only [h3967, h3968, h4004, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4006 | h4006
            · linarith only [h2, h3, h3967, h3968, h4006, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4008 | h4008
              · linarith only [h2, h3, h4008, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4010 | h4010
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4011 | h4011
                  · linarith only [h0, h3968, h4011, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4013 | h4013
                    · linarith only [h0, h4002, h4013, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4015 | h4015
                      · linarith only [h1, h3, h4004, h4013, h4015, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4017 | h4017
                        · linarith only [h1, h4006, h4017, hlam]
                        · linarith only [h2, h3, h4010, h4011, h4017, hc23, hc35, hlam, hphi]
                · linarith only [h3967, h3968, h4010, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4021 | h4021
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4022 | h4022
        · linarith only [h1, h3, h3967, h4022, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4024 | h4024
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4025 | h4025
            · linarith only [h1, h3, h4025, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4027 | h4027
              · linarith only [h1, h3, h3967, h4021, h4027, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4029 | h4029
                · linarith only [h0, h3, h3967, h4029, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4031 | h4031
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4032 | h4032
                    · linarith only [h0, h3, h4022, h4032, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4034 | h4034
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4035 | h4035
                        · linarith only [h1, h3, h4025, h4032, h4035, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4037 | h4037
                          · linarith only [h2, h3, h4027, h4037, hlam]
                          · linarith only [h1, h3, h4029, h4031, h4037, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h4024, h4029, h4031, h4032, h4034, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h3967, h4021, h4031, hc12, hc23, hlam, hphi]
          · linarith only [h3967, h4021, h4024, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4043 | h4043
        · linarith only [h1, h3, h3967, h4043, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4045 | h4045
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4046 | h4046
            · linarith only [h1, h3, h4046, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4048 | h4048
              · linarith only [h1, h3, h4045, h4048, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4050 | h4050
                · linarith only [h0, h3, h3967, h4050, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4052 | h4052
                  · linarith only [h0, h4021, h4052, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4054 | h4054
                    · linarith only [h0, h3, h4043, h4054, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4056 | h4056
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4057 | h4057
                        · linarith only [h1, h3, h4021, h4045, h4046, h4057, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4059 | h4059
                          · linarith only [h1, h3, h4048, h4056, h4059, hlam]
                          · linarith only [h1, h3, h4056, h4059, hc34, hc45, hlam, hphi]
                      · linarith only [h4045, h4046, h4056, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4063 | h4063
            · linarith only [h1, h3, h4063, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4065 | h4065
              · linarith only [h2, h3, h4065, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4067 | h4067
                · linarith only [h0, h3, h3967, h4067, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4069 | h4069
                  · linarith only [h0, h4021, h4069, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4071 | h4071
                    · linarith only [h0, h3, h4043, h4071, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4073 | h4073
                      · linarith only [h1, h3, h4045, h4071, h4073, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4075 | h4075
                        · linarith only [h1, h3, h4063, h4075, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4077 | h4077
                          · linarith only [h2, h3, h4065, h4075, h4077, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4079 | h4079
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4080 | h4080
                              · linarith only [h0, h3, h4075, h4080, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h3967, h4045, h4079, h4080, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4083 | h4083
                              · linarith only [h0, h3967, h4063, h4079, h4083, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4085 | h4085
                                · linarith only [h2, h3, h4067, h4073, h4077, h4085, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4087 | h4087
                                  · linarith only [h0, h3967, h4079, h4085, h4087, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h3967, h4079, h4087, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8758000 in
set_option maxHeartbeats 8758000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_22_13_15_H_I_L_I_L_I_s2 m hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4090 | h4090
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4091 | h4091
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4092 | h4092
        · linarith only [h0, h2, h4092, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4094 | h4094
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4095 | h4095
            · linarith only [h1, h2, h4095, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4097 | h4097
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4098 | h4098
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4099 | h4099
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4100 | h4100
                    · linarith only [h0, h2, h4092, h4100, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4102 | h4102
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4103 | h4103
                        · linarith only [h1, h2, h4095, h4103, hlam]
                        · linarith only [h0, h2, h4099, h4103, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h4094, h4099, h4100, h4102, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h4091, h4092, h4099, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h4097, h4098, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4109 | h4109
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4110 | h4110
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4111 | h4111
                    · linarith only [h0, h2, h4092, h4111, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4113 | h4113
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4114 | h4114
                        · linarith only [h1, h2, h4095, h4114, hlam]
                        · linarith only [h0, h2, h4110, h4114, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h4094, h4110, h4113, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4091, h4092, h4110, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h4094, h4109, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4120 | h4120
            · linarith only [h1, h2, h4120, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4122 | h4122
              · linarith only [h4091, h4094, h4122, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4124 | h4124
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4125 | h4125
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4126 | h4126
                    · linarith only [h0, h2, h4092, h4126, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4128 | h4128
                      · linarith only [h0, h4094, h4128, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4130 | h4130
                        · linarith only [h0, h2, h4120, h4125, h4130, hlam]
                        · linarith only [h2, h4090, h4125, h4128, h4130, hc23, hc34, hlam, hphi]
                  · linarith only [h4091, h4094, h4125, hc12, hc25, hlam, hphi]
                · linarith only [h2, h4090, h4124, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4135 | h4135
        · linarith only [h0, h2, h4135, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4137 | h4137
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4138 | h4138
            · linarith only [h1, h2, h4138, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4140 | h4140
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4141 | h4141
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4142 | h4142
                  · linarith only [h0, h2, h4091, h4142, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4144 | h4144
                    · linarith only [h0, h2, h4135, h4144, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4146 | h4146
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4147 | h4147
                        · linarith only [h1, h2, h4091, h4138, h4147, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4149 | h4149
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4150 | h4150
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4151 | h4151
                              · linarith only [h0, h2, h4146, h4147, h4151, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4153 | h4153
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4154 | h4154
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4155 | h4155
                                    · rcases h2bigk with h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c | h4156c
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4146, h4153, h4155, hc02, hc45, hlam, hphi, ht0b, ht5b, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4091, hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4135, hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4091, h4151, h4153, h4155, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h0, hlam, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4142, hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4144, hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h1, h4142, h4153, h4155, hc01, hc45, hlam, hphi, ht0b, ht5b, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4151, hc02, hc34, hlam, hphi, ht23, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4151, hc12, hc34, hlam, hphi, ht23, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4151, hlam, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4151, h4153, h4155, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4151, hc02, hc34, hlam, hphi, ht23, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4146, h4151, h4153, h4155, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4151, hc23, hc34, hlam, hphi, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        rcases p4156_3 (m.d 0 2) (by simp) with h4176 | h4176
                                        · linarith only [h4135, h4176, hlam]
                                        · linarith only [h4137, h4176, hlam]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4137, hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4146, hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4153, hlam, p4156_0]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [h4154, hlam, p4156_1]
                                      · have p4156_0 := h4156c.1
                                        have p4156_1 := h4156c.2.1
                                        have p4156_2 := h4156c.2.2.1
                                        have p4156_3 := h4156c.2.2.2
                                        linarith only [hlam, p4156_0]
                                    · linarith only [h1, h2, h4144, h4151, h4155, hc13, hc45, hlam, hphi, ht34]
                                  · linarith only [h1, h2, h4142, h4144, h4146, h4150, h4154, hlam]
                                · linarith only [h1, h2, h4091, h4140, h4153, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h2, h4137, h4141, h4149, h4150, hc02, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h2, h4140, h4142, h4146, h4147, h4149, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h4091, h4137, h4146, hc12, hc23, hlam, hphi]
                · linarith only [h1, h2, h4091, h4137, h4141, hlam]
              · linarith only [h4091, h4137, h4140, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4192 | h4192
            · linarith only [h1, h2, h4192, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4194 | h4194
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4195 | h4195
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4196 | h4196
                  · linarith only [h0, h4091, h4196, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4198 | h4198
                    · linarith only [h0, h4135, h4198, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4200 | h4200
                      · linarith only [h0, h2, h4137, h4198, h4200, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4202 | h4202
                        · linarith only [h1, h2, h4192, h4202, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4204 | h4204
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4205 | h4205
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4206 | h4206
                              · linarith only [h1, h2, h4200, h4202, h4204, h4206, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4208 | h4208
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4209 | h4209
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4210 | h4210
                                    · rcases h2bigk with h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4137, hc12, hc25, hlam, hphi, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4091, hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4135, hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4137, hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h0, hlam, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4196, hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4198, hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4200, hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4206, hc02, hc34, hlam, hphi, ht23, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4206, hc12, hc34, hlam, hphi, ht23, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4206, hlam, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4206, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h0, hc12, hc24, hlam, hphi, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [hc12, hc24, hlam, hphi, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4206, hc23, hc34, hlam, hphi, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h0, h4137, h4206, hc12, hc34, hlam, hphi, ht23, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h0, h4208, hc12, hc23, hlam, hphi, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4208, hc12, hc23, hlam, hphi, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4208, hlam, p4211_0]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [h4209, hlam, p4211_1]
                                      · have p4211_0 := h4211c.1
                                        have p4211_1 := h4211c.2.1
                                        have p4211_2 := h4211c.2.2.1
                                        have p4211_3 := h4211c.2.2.2
                                        linarith only [hlam, p4211_0]
                                    · linarith only [h0, h4091, h4206, h4210, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h2, h4198, h4204, h4205, h4209, hlam]
                                · linarith only [h1, h2, h4204, h4208, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1, h2, h4195, h4204, h4205, hc05, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h2, h4194, h4202, h4204, hc13, hc34, hlam, hphi]
                · linarith only [h1, h2, h4194, h4195, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4243 | h4243
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4244 | h4244
                  · linarith only [h0, h4091, h4244, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4246 | h4246
                    · linarith only [h0, h4135, h4246, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4248 | h4248
                      · linarith only [h0, h4137, h4248, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4250 | h4250
                        · linarith only [h1, h2, h4192, h4250, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4252 | h4252
                          · linarith only [h1, h4194, h4252, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4254 | h4254
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4255 | h4255
                              · linarith only [h0, h2, h4250, h4255, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4257 | h4257
                                · linarith only [h4091, h4194, h4255, h4257, hc02, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4259 | h4259
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4260 | h4260
                                    · rcases h2bigk with h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4091, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4135, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4137, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, hlam, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4244, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4246, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4248, hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4257, h4260, hc02, hc34, hlam, hphi, ht23, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4257, h4260, hc12, hc34, hlam, hphi, ht23, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4255, hlam, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4257, hlam, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, hc12, hc24, hlam, hphi, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hc12, hc24, hlam, hphi, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4255, hc23, hc34, hlam, hphi, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h4091, h4255, h4257, hc12, hc34, hlam, hphi, ht23, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, hc12, hc25, hlam, hphi, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hc12, hc25, hlam, hphi, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h0, h4091, h4257, h4260, hc12, hc34, hlam, hphi, ht23, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [h4259, hlam, p4261_1]
                                      · have p4261_0 := h4261c.1
                                        have p4261_1 := h4261c.2.1
                                        have p4261_2 := h4261c.2.2.1
                                        have p4261_3 := h4261c.2.2.2
                                        linarith only [hlam, p4261_0]
                                    · linarith only [h0, h2, h4246, h4255, h4260, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h2, h4090, h4246, h4254, h4259, hlam]
                            · linarith only [h2, h4090, h4244, h4252, h4254, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h4090, h4243, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4291 | h4291
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4292 | h4292
        · linarith only [h0, h2, h4292, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4294 | h4294
          · linarith only [h0, h4090, h4294, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4296 | h4296
            · linarith only [h0, h2, h4291, h4296, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4298 | h4298
              · linarith only [h0, h4090, h4291, h4298, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4300 | h4300
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4301 | h4301
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4302 | h4302
                    · linarith only [h0, h2, h4292, h4302, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4304 | h4304
                      · linarith only [h0, h4090, h4294, h4304, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4306 | h4306
                        · linarith only [h0, h4090, h4296, h4300, h4301, h4306, hlam]
                        · linarith only [h0, h2, h4301, h4306, hc23, hc34, hlam, hphi]
                  · linarith only [h4291, h4292, h4301, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4310 | h4310
                  · linarith only [h0, h2, h4300, h4310, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h4291, h4300, h4310, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4313 | h4313
        · linarith only [h1, h2, h4291, h4313, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4315 | h4315
          · linarith only [h1, h4090, h4291, h4315, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4317 | h4317
            · linarith only [h1, h2, h4317, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4319 | h4319
              · linarith only [h1, h4090, h4319, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4321 | h4321
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4322 | h4322
                  · linarith only [h0, h2, h4291, h4322, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4324 | h4324
                    · linarith only [h1, h4090, h4313, h4321, h4322, h4324, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4326 | h4326
                      · linarith only [h1, h4090, h4315, h4322, h4326, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4328 | h4328
                        · linarith only [h1, h4090, h4317, h4321, h4328, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4330 | h4330
                          · linarith only [h1, h4090, h4319, h4330, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4332 | h4332
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4333 | h4333
                              · linarith only [h1, h4090, h4322, h4328, h4332, h4333, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4335 | h4335
                                · linarith only [h1, h4090, h4322, h4330, h4335, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4337 | h4337
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4338 | h4338
                                    · rcases h2bigk with h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c | h4339c
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4291, h4335, h4338, hc12, hc34, hlam, hphi, ht23, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4291, hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4313, hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4315, hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h0, hlam, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4322, hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4324, hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4326, hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4335, h4338, hc02, hc34, hlam, hphi, ht23, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4335, h4338, hc12, hc34, hlam, hphi, ht23, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4333, hlam, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4335, hlam, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h0, hc12, hc24, hlam, hphi, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [hc12, hc24, hlam, hphi, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4333, hc23, hc34, hlam, hphi, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [hlam, p4339_0]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h1, h4090, h4322, h4326, h4333, hc12, hc34, hlam, hphi, ht23, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h0, hc12, hc25, hlam, hphi, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [hc12, hc25, hlam, hphi, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h0, h4291, h4335, h4338, hc12, hc34, hlam, hphi, ht23, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [h4337, hlam, p4339_1]
                                      · have p4339_0 := h4339c.1
                                        have p4339_1 := h4339c.2.1
                                        have p4339_2 := h4339c.2.2.1
                                        have p4339_3 := h4339c.2.2.2
                                        linarith only [hlam, p4339_0]
                                    · linarith only [h4313, h4321, h4333, h4338, hlam]
                                  · linarith only [h2, h4321, h4324, h4337, hlam]
                            · linarith only [h2, h4321, h4332, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4368 | h4368
                  · linarith only [h0, h4291, h4368, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4370 | h4370
                    · linarith only [h0, h2, h4321, h4370, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4372 | h4372
                      · linarith only [h1, h2, h4315, h4321, h4368, h4372, hc02, hc45, hlam, hphi, ht23, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4374 | h4374
                        · linarith only [h1, h2, h4317, h4321, h4374, hc03, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4376 | h4376
                          · linarith only [h1, h4319, h4376, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4378 | h4378
                            · linarith only [h0, h2, h4321, h4374, h4378, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2, h4368, h4378, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
