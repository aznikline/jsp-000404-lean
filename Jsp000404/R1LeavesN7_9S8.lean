import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h3689 | h3689
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3690 | h3690
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3691 | h3691
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3692 | h3692
        · linarith only [h0, h3692, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3694 | h3694
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3695 | h3695
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3696 | h3696
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3697 | h3697
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3698 | h3698
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3699 | h3699
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3700 | h3700
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3701 | h3701
                        · rcases h3bigk with h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c | h3702c
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3692, h3694, h3698, h3701, hc03, hc45, hlam, hphi, ht0b, ht5b, p3702_1]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h4, hlam, p3702_1]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            rcases p3702_3 (m.d 0 3) (by simp) with h3706 | h3706
                            · rcases p3702_3 (m.d 1 3) (by simp) with h3707 | h3707
                              · linarith only [h1, h3707, hlam]
                              · linarith only [h3695, h3707, hlam]
                            · linarith only [h3706, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            rcases p3702_3 (m.d 0 3) (by simp) with h3711 | h3711
                            · rcases p3702_3 (m.d 1 3) (by simp) with h3712 | h3712
                              · linarith only [h1, h3712, hlam]
                              · linarith only [h3696, h3712, hlam]
                            · linarith only [h3711, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h1, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3692, hlam, p3702_1]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h1, h3701, hc01, hc45, hlam, hphi, ht0b, ht5b, p3702_1]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            rcases p3702_3 (m.d 0 3) (by simp) with h3720 | h3720
                            · rcases p3702_3 (m.d 1 3) (by simp) with h3721 | h3721
                              · rcases p3702_3 (m.d 2 3) (by simp) with h3722 | h3722
                                · rcases p3702_3 (m.d 3 4) (by simp) with h3723 | h3723
                                  · linarith only [h3695, h3723, hlam]
                                  · linarith only [h3701, h3723, hlam]
                                · linarith only [h3699, h3722, hlam]
                              · linarith only [h3721, hlam, p3702_0]
                            · linarith only [h3690, h3720, hlam]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h0, h3694, h3698, h3701, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3702_1]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3692, h3694, h3698, h3701, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3702_1]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            rcases p3702_3 (m.d 0 3) (by simp) with h3732 | h3732
                            · linarith only [h3732, h4, hlam]
                            · linarith only [h3689, h3732, hlam]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            rcases p3702_3 (m.d 0 3) (by simp) with h3735 | h3735
                            · linarith only [h3735, h4, hlam]
                            · linarith only [h3690, h3735, hlam]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3689, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3695, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3698, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h0, h3694, h3698, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p3702_1]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3690, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3696, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3699, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [h3701, hlam, p3702_0]
                          · have p3702_0 := h3702c.1
                            have p3702_1 := h3702c.2.1
                            have p3702_2 := h3702c.2.2.1
                            have p3702_3 := h3702c.2.2.2
                            linarith only [hlam, p3702_0]
                        · linarith only [h0, h3694, h3700, h3701, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3749 | h3749
                        · linarith only [h1, h3695, h3700, h3749, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h3bigk with h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c | h3751c
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3692, h3694, h3697, h3698, h3700, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3751_1]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h4, hlam, p3751_1]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            rcases p3751_3 (m.d 0 3) (by simp) with h3755 | h3755
                            · rcases p3751_3 (m.d 1 3) (by simp) with h3756 | h3756
                              · linarith only [h1, h3756, hlam]
                              · linarith only [h3695, h3756, hlam]
                            · linarith only [h3755, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            rcases p3751_3 (m.d 0 3) (by simp) with h3760 | h3760
                            · rcases p3751_3 (m.d 1 3) (by simp) with h3761 | h3761
                              · linarith only [h1, h3761, hlam]
                              · linarith only [h3696, h3761, hlam]
                            · linarith only [h3760, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h1, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3692, hlam, p3751_1]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            rcases p3751_3 (m.d 0 3) (by simp) with h3768 | h3768
                            · rcases p3751_3 (m.d 1 3) (by simp) with h3769 | h3769
                              · rcases p3751_3 (m.d 2 3) (by simp) with h3770 | h3770
                                · rcases p3751_3 (m.d 3 4) (by simp) with h3771 | h3771
                                  · linarith only [h3771, hlam, p3751_0]
                                  · rcases p3751_3 (m.d 3 5) (by simp) with h3773 | h3773
                                    · linarith only [h3696, h3773, hlam]
                                    · linarith only [h3749, h3773, hlam]
                                · linarith only [h3698, h3770, hlam]
                              · linarith only [h3769, hlam, p3751_0]
                            · linarith only [h3689, h3768, hlam]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            rcases p3751_3 (m.d 0 3) (by simp) with h3779 | h3779
                            · rcases p3751_3 (m.d 1 3) (by simp) with h3780 | h3780
                              · rcases p3751_3 (m.d 2 3) (by simp) with h3781 | h3781
                                · rcases p3751_3 (m.d 3 4) (by simp) with h3782 | h3782
                                  · linarith only [h3695, h3782, hlam]
                                  · rcases p3751_3 (m.d 3 5) (by simp) with h3784 | h3784
                                    · linarith only [h3784, hlam, p3751_0]
                                    · rcases h4bigk with h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3688, h3697, h3698, h3700, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3688, h3698, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3688, h3698, h3700, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h2, hlam, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h0, h3694, h3698, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h0, h3694, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h0, h3694, h3698, h3700, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3688, hlam, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3694, hlam, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3700, hc34, hc45, hlam, hphi, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3700, hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3689, hlam, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3695, hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3698, hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3749, hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3691, hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h3697, hlam, p3786_0]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [hc24, hc45, hlam, hphi, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [h0, h3694, h3697, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3786_1]
                                      · have p3786_0 := h3786c.1
                                        have p3786_1 := h3786c.2.1
                                        have p3786_2 := h3786c.2.2.1
                                        have p3786_3 := h3786c.2.2.2
                                        linarith only [hlam, p3786_0]
                                · linarith only [h3699, h3781, hlam]
                              · linarith only [h3780, hlam, p3751_0]
                            · linarith only [h3690, h3779, hlam]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h1, h3692, h3694, h3697, h3698, h3700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3751_1]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3692, h3694, h3697, h3698, h3700, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3751_1]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h0, h3694, h3697, h3698, h3700, h4, hlam, p3751_2]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            rcases p3751_3 (m.d 0 3) (by simp) with h3819 | h3819
                            · linarith only [h3819, h4, hlam]
                            · linarith only [h3690, h3819, hlam]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3689, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3695, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3698, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3749, hlam, p3751_1]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3690, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3696, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h3699, hlam, p3751_0]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [h1, h3696, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3751_1]
                          · have p3751_0 := h3751c.1
                            have p3751_1 := h3751c.2.1
                            have p3751_2 := h3751c.2.2.1
                            have p3751_3 := h3751c.2.2.2
                            linarith only [hlam, p3751_0]
                    · linarith only [h1, h3696, h3699, h4, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h3689, h3698, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3834 | h3834
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3835 | h3835
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3836 | h3836
                      · linarith only [h3694, h3697, h3836, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3838 | h3838
                        · linarith only [h3694, h3697, h3834, h3838, hlam]
                        · rcases h3bigk with h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c | h3840c
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 3) (by simp) with h3842 | h3842
                            · rcases p3840_3 (m.d 1 3) (by simp) with h3843 | h3843
                              · linarith only [h1, h3843, hlam]
                              · rcases p3840_3 (m.d 2 3) (by simp) with h3845 | h3845
                                · rcases p3840_3 (m.d 3 4) (by simp) with h3846 | h3846
                                  · linarith only [h3689, h3846, hlam]
                                  · rcases p3840_3 (m.d 3 5) (by simp) with h3848 | h3848
                                    · linarith only [h3690, h3848, hlam]
                                    · rcases h4bigk with h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h3694, h3834, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h3834, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h3694, h3697, h3834, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h2, hlam, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3697, h3834, hc34, hc45, hlam, hphi, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h3691, h3697, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3697, hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, hlam, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3694, hlam, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3836, hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3689, hlam, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3695, hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3834, hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3838, hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3691, hlam, p3850_0]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h3691, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h3691, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [h3688, h3691, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3850_1]
                                      · have p3850_0 := h3850c.1
                                        have p3850_1 := h3850c.2.1
                                        have p3850_2 := h3850c.2.2.1
                                        have p3850_3 := h3850c.2.2.2
                                        linarith only [hlam, p3850_0]
                                · linarith only [h3692, h3845, hlam]
                            · linarith only [h1, h3842, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h4, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 3) (by simp) with h3879 | h3879
                            · rcases p3840_3 (m.d 1 3) (by simp) with h3880 | h3880
                              · linarith only [h1, h3880, hlam]
                              · linarith only [h3695, h3880, hlam]
                            · linarith only [h3879, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 3) (by simp) with h3884 | h3884
                            · rcases p3840_3 (m.d 1 3) (by simp) with h3885 | h3885
                              · linarith only [h1, h3885, hlam]
                              · linarith only [h3696, h3885, hlam]
                            · linarith only [h3884, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h1, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3692, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 3) (by simp) with h3892 | h3892
                            · rcases p3840_3 (m.d 1 3) (by simp) with h3893 | h3893
                              · rcases p3840_3 (m.d 2 3) (by simp) with h3894 | h3894
                                · rcases p3840_3 (m.d 3 4) (by simp) with h3895 | h3895
                                  · linarith only [h3895, hlam, p3840_0]
                                  · rcases p3840_3 (m.d 3 5) (by simp) with h3897 | h3897
                                    · linarith only [h3696, h3897, hlam]
                                    · linarith only [h3838, h3897, hlam]
                                · linarith only [h3834, h3894, hlam]
                              · linarith only [h3893, hlam, p3840_0]
                            · linarith only [h3689, h3892, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 3) (by simp) with h3903 | h3903
                            · rcases p3840_3 (m.d 1 3) (by simp) with h3904 | h3904
                              · rcases p3840_3 (m.d 2 3) (by simp) with h3905 | h3905
                                · rcases p3840_3 (m.d 3 4) (by simp) with h3906 | h3906
                                  · linarith only [h3695, h3906, hlam]
                                  · rcases p3840_3 (m.d 3 5) (by simp) with h3908 | h3908
                                    · linarith only [h3908, hlam, p3840_0]
                                    · rcases h4bigk with h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, h3697, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h2, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h2, h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3697, hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3694, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3694, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3836, hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3689, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3695, hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3834, hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3838, hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3691, hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, h3691, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, h3691, h3834, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, h3691, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                · linarith only [h3835, h3905, hlam]
                              · linarith only [h3904, hlam, p3840_0]
                            · linarith only [h3690, h3903, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3688, h3691, h3694, h3697, h3834, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 3) (by simp) with h3940 | h3940
                            · linarith only [h3940, h4, hlam]
                            · linarith only [h1, h3940, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3688, h3691, h3694, h3697, h3834, h4, hlam, p3840_2]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            rcases p3840_3 (m.d 0 3) (by simp) with h3945 | h3945
                            · linarith only [h3945, h4, hlam]
                            · linarith only [h3690, h3945, hlam]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3689, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3695, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3834, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3838, hlam, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3690, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3696, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h3835, hlam, p3840_0]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [h1, h3696, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3840_1]
                          · have p3840_0 := h3840c.1
                            have p3840_1 := h3840c.2.1
                            have p3840_2 := h3840c.2.2.1
                            have p3840_3 := h3840c.2.2.2
                            linarith only [hlam, p3840_0]
                    · linarith only [h3688, h3691, h3696, h3697, h3835, h4, hlam]
                  · linarith only [h3688, h3691, h3694, h3697, h3834, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3960 | h3960
                · linarith only [h3692, h3694, h3696, h3960, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3962 | h3962
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3963 | h3963
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3964 | h3964
                      · linarith only [h3688, h3690, h3691, h3692, h3694, h3696, h3960, h3964, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h3688, h3691, h3692, h3696, h3963, h3964, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h3688, h3690, h3691, h3963, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3689, h3962, h4, hlam]
            · linarith only [h3692, h3694, h3695, hlam]
          · linarith only [h3688, h3694, h4, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3971 | h3971
        · linarith only [h0, h3688, h3971, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3973 | h3973
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3974 | h3974
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3975 | h3975
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3976 | h3976
                · linarith only [h2, h3691, h3976, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3978 | h3978
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3979 | h3979
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3980 | h3980
                      · linarith only [h2, h3691, h3973, h3980, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3982 | h3982
                        · linarith only [h2, h3691, h3973, h3978, h3982, hlam]
                        · rcases h3bigk with h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c | h3984c
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h3986 | h3986
                            · rcases p3984_3 (m.d 1 3) (by simp) with h3987 | h3987
                              · linarith only [h1, h3987, hlam]
                              · rcases p3984_3 (m.d 2 3) (by simp) with h3989 | h3989
                                · rcases p3984_3 (m.d 3 4) (by simp) with h3990 | h3990
                                  · linarith only [h3689, h3990, hlam]
                                  · rcases p3984_3 (m.d 3 5) (by simp) with h3992 | h3992
                                    · linarith only [h3690, h3992, hlam]
                                    · rcases h4bigk with h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c | h3994c
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3691, hc14, hc45, hlam, hphi, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3691, h3978, hc34, hc45, hlam, hphi, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3691, hc34, hc45, hlam, hphi, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3691, hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h2, hlam, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h2, h3978, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3971, h3973, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3984_1, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3976, hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3688, hlam, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3973, hlam, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3688, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3980, hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3689, hlam, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3974, hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3978, hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3982, hlam, p3994_0]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [hc04, hc45, hlam, hphi, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3973, hc24, hc45, hlam, hphi, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [h3978, hc34, hc45, hlam, hphi, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p3994_1]
                                      · have p3994_0 := h3994c.1
                                        have p3994_1 := h3994c.2.1
                                        have p3994_2 := h3994c.2.2.1
                                        have p3994_3 := h3994c.2.2.2
                                        linarith only [hlam, p3994_0]
                                · linarith only [h3971, h3989, hlam]
                            · linarith only [h1, h3986, hlam]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h4, hlam, p3984_1]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4023 | h4023
                            · rcases p3984_3 (m.d 1 3) (by simp) with h4024 | h4024
                              · linarith only [h1, h4024, hlam]
                              · linarith only [h3974, h4024, hlam]
                            · linarith only [h4023, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4028 | h4028
                            · rcases p3984_3 (m.d 1 3) (by simp) with h4029 | h4029
                              · linarith only [h1, h4029, hlam]
                              · linarith only [h3975, h4029, hlam]
                            · linarith only [h4028, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h1, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3971, hlam, p3984_1]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4036 | h4036
                            · rcases p3984_3 (m.d 1 3) (by simp) with h4037 | h4037
                              · rcases p3984_3 (m.d 2 3) (by simp) with h4038 | h4038
                                · rcases p3984_3 (m.d 3 4) (by simp) with h4039 | h4039
                                  · linarith only [h4039, hlam, p3984_0]
                                  · rcases p3984_3 (m.d 3 5) (by simp) with h4041 | h4041
                                    · linarith only [h3975, h4041, hlam]
                                    · linarith only [h3982, h4041, hlam]
                                · linarith only [h3978, h4038, hlam]
                              · linarith only [h4037, hlam, p3984_0]
                            · linarith only [h3689, h4036, hlam]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4047 | h4047
                            · rcases p3984_3 (m.d 1 3) (by simp) with h4048 | h4048
                              · rcases p3984_3 (m.d 2 3) (by simp) with h4049 | h4049
                                · rcases p3984_3 (m.d 3 4) (by simp) with h4050 | h4050
                                  · linarith only [h3974, h4050, hlam]
                                  · rcases p3984_3 (m.d 3 5) (by simp) with h4052 | h4052
                                    · linarith only [h4052, hlam, p3984_0]
                                    · rcases h4bigk with h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c | h4054c
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3688, h3973, h3978, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3688, h3978, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3691, hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h2, hlam, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h2, h3978, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h2, h3691, hc34, hc45, hlam, hphi, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3976, hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3688, hlam, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3973, hlam, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3980, hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3689, hlam, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3974, hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3978, hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3982, hlam, p4054_0]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [hc04, hc45, hlam, hphi, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3973, hc24, hc45, hlam, hphi, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [h3978, hc34, hc45, hlam, hphi, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p4054_1]
                                      · have p4054_0 := h4054c.1
                                        have p4054_1 := h4054c.2.1
                                        have p4054_2 := h4054c.2.2.1
                                        have p4054_3 := h4054c.2.2.2
                                        linarith only [hlam, p4054_0]
                                · linarith only [h3979, h4049, hlam]
                              · linarith only [h4048, hlam, p3984_0]
                            · linarith only [h3690, h4047, hlam]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4083 | h4083
                            · linarith only [h4, h4083, hlam]
                            · rcases p3984_3 (m.d 1 3) (by simp) with h4085 | h4085
                              · linarith only [h3971, h4085, hlam]
                              · rcases p3984_3 (m.d 2 3) (by simp) with h4087 | h4087
                                · rcases p3984_3 (m.d 3 4) (by simp) with h4088 | h4088
                                  · linarith only [h3978, h4088, hlam]
                                  · rcases p3984_3 (m.d 3 5) (by simp) with h4090 | h4090
                                    · linarith only [h3979, h4090, hlam]
                                    · rcases h4bigk with h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c | h4092c
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3688, h3973, h3978, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3984_1, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3688, h3978, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3984_1, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3984_1, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3691, hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h2, hlam, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h2, h3978, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h2, h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3984_1, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3976, hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3688, hlam, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3973, hlam, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3688, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3984_1, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3980, hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3689, hlam, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3974, hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3978, hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3982, hlam, p4092_0]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [hc04, hc45, hlam, hphi, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3973, hc24, hc45, hlam, hphi, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [h3978, hc34, hc45, hlam, hphi, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p4092_1]
                                      · have p4092_0 := h4092c.1
                                        have p4092_1 := h4092c.2.1
                                        have p4092_2 := h4092c.2.2.1
                                        have p4092_3 := h4092c.2.2.2
                                        linarith only [hlam, p4092_0]
                                · linarith only [h4, h4087, hlam]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4119 | h4119
                            · linarith only [h4, h4119, hlam]
                            · linarith only [h1, h4119, hlam]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4123 | h4123
                            · linarith only [h4, h4123, hlam]
                            · linarith only [h3689, h4123, hlam]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            rcases p3984_3 (m.d 0 3) (by simp) with h4126 | h4126
                            · linarith only [h4, h4126, hlam]
                            · linarith only [h3690, h4126, hlam]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3689, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3974, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3978, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3982, hlam, p3984_1]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3690, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3975, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h3979, hlam, p3984_0]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [h1, h3975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3984_1]
                          · have p3984_0 := h3984c.1
                            have p3984_1 := h3984c.2.1
                            have p3984_2 := h3984c.2.2.1
                            have p3984_3 := h3984c.2.2.2
                            linarith only [hlam, p3984_0]
                    · linarith only [h1, h3975, h3979, h4, hlam]
                  · linarith only [h3689, h3978, h4, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4141 | h4141
                · linarith only [h2, h3691, h4141, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4143 | h4143
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4144 | h4144
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4145 | h4145
                      · linarith only [h3690, h3691, h3971, h3973, h3975, h4, h4145, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4147 | h4147
                        · linarith only [h3688, h3690, h3691, h3971, h3975, h4, h4143, h4147, hc12, hc23, hlam, hphi]
                        · rcases h3bigk with h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c | h4149c
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            rcases p4149_3 (m.d 0 3) (by simp) with h4151 | h4151
                            · rcases p4149_3 (m.d 1 3) (by simp) with h4152 | h4152
                              · linarith only [h1, h4152, hlam]
                              · rcases p4149_3 (m.d 2 3) (by simp) with h4154 | h4154
                                · rcases p4149_3 (m.d 3 4) (by simp) with h4155 | h4155
                                  · linarith only [h3689, h4155, hlam]
                                  · rcases p4149_3 (m.d 3 5) (by simp) with h4157 | h4157
                                    · linarith only [h3690, h4157, hlam]
                                    · linarith only [h3975, h4157, hlam]
                                · linarith only [h3971, h4154, hlam]
                            · linarith only [h1, h4151, hlam]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h4, hlam, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3690, h3971, h3973, h3975, h4143, hlam, p4149_2]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h1, h3971, h3973, h3975, h4143, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h1, hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3971, hlam, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3690, h3691, h3975, hc34, hc45, hlam, hphi, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3975, hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3690, h3975, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            rcases p4149_3 (m.d 0 3) (by simp) with h4171 | h4171
                            · linarith only [h4, h4171, hlam]
                            · linarith only [h1, h4171, hlam]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3690, h3971, h3973, h3975, h4, h4143, hlam, p4149_2]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3971, h3973, h3975, h4143, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3689, hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3974, hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h4143, hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h4147, hlam, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3690, hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h3690, h3971, h3973, h4143, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4149_1]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [h4144, hlam, p4149_0]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            rcases p4149_3 (m.d 0 3) (by simp) with h4185 | h4185
                            · rcases p4149_3 (m.d 1 3) (by simp) with h4186 | h4186
                              · linarith only [h3975, h4186, hlam]
                              · linarith only [h3974, h4186, hlam]
                            · linarith only [h3689, h4185, hlam]
                          · have p4149_0 := h4149c.1
                            have p4149_1 := h4149c.2.1
                            have p4149_2 := h4149c.2.2.1
                            have p4149_3 := h4149c.2.2.2
                            linarith only [hlam, p4149_0]
                    · linarith only [h3690, h4, h4144, hlam]
                  · linarith only [h3689, h4, h4143, hlam]
            · linarith only [h3689, h3691, h3971, h3973, h3974, hc24, hc45, hlam, hphi]
          · linarith only [h3688, h3973, h4, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4195 | h4195
      · linarith only [h3688, h3690, h4, h4195, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4197 | h4197
        · linarith only [h0, h3688, h4, h4197, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4199 | h4199
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4200 | h4200
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4201 | h4201
              · linarith only [h1, h3690, h4201, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4203 | h4203
                · linarith only [h2, h3688, h3690, h4, h4195, h4203, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4205 | h4205
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4206 | h4206
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4207 | h4207
                      · linarith only [h0, h2, h3690, h4, h4195, h4199, h4207, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4209 | h4209
                        · linarith only [h3688, h3690, h4, h4205, h4206, h4207, h4209, hlam]
                        · rcases h3bigk with h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3690, h4197, h4206, hc12, hc23, hlam, hphi, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3690, h4206, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3690, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h1, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4197, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h1, h3690, h4206, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4201, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            rcases p4211_3 (m.d 0 3) (by simp) with h4222 | h4222
                            · linarith only [h4, h4222, hlam]
                            · rcases p4211_3 (m.d 1 3) (by simp) with h4224 | h4224
                              · linarith only [h4197, h4224, hlam]
                              · rcases p4211_3 (m.d 2 3) (by simp) with h4226 | h4226
                                · rcases p4211_3 (m.d 3 4) (by simp) with h4227 | h4227
                                  · linarith only [h4205, h4227, hlam]
                                  · rcases p4211_3 (m.d 3 5) (by simp) with h4229 | h4229
                                    · linarith only [h4206, h4229, hlam]
                                    · linarith only [h3690, h4229, hlam]
                                · linarith only [h4, h4226, hlam]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            rcases p4211_3 (m.d 0 3) (by simp) with h4233 | h4233
                            · linarith only [h4, h4233, hlam]
                            · linarith only [h1, h4233, hlam]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h0, h3690, h4, h4199, h4205, h4206, hlam, p4211_2]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3690, h4, hc02, hc23, hlam, hphi, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3689, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4200, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4205, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4209, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h0, h4, h4199, h4205, h4206, h4207, hc34, hc45, hlam, hphi, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4197, h4199, h4205, h4206, h4207, hc34, hc45, hlam, hphi, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4206, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            rcases p4211_3 (m.d 0 3) (by simp) with h4247 | h4247
                            · linarith only [h3690, h4247, hlam]
                            · linarith only [h3689, h4247, hlam]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4251 | h4251
                      · linarith only [h0, h4, h4199, h4206, h4251, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4253 | h4253
                        · linarith only [h0, h4, h4199, h4205, h4206, h4251, h4253, hlam]
                        · linarith only [h0, h4, h4199, h4205, h4206, h4253, hc34, hc45, hlam, hphi]
                  · linarith only [h0, h3689, h4, h4199, h4205, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h3689, h3690, h4197, h4199, h4200, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h3688, h4, h4199, hc12, hc23, hlam, hphi]
  · linarith only [h3688, h3689, h4, hlam]

end R2N4
