import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h20699 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h20700 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20701 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 3 5 (by decide) (by decide) with h20702 | h20702
  · rcases m.htr 0 4 5 (by decide) (by decide) with h20703 | h20703
    · rcases m.htr 1 2 3 (by decide) (by decide) with h20704 | h20704
      · rcases m.htr 1 2 4 (by decide) (by decide) with h20705 | h20705
        · rcases m.htr 1 2 5 (by decide) (by decide) with h20706 | h20706
          · rcases m.htr 1 3 4 (by decide) (by decide) with h20707 | h20707
            · rcases m.htr 1 3 5 (by decide) (by decide) with h20708 | h20708
              · rcases m.htr 1 4 5 (by decide) (by decide) with h20709 | h20709
                · rcases m.htr 2 3 4 (by decide) (by decide) with h20710 | h20710
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h20711 | h20711
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h20712 | h20712
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h20713 | h20713
                        · rcases h0bigk with h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c | h20714c
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h0, hlam, p20714_1]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h15532, hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h18443, hlam, p20714_1]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20719 | h20719
                            · rcases p20714_3 (m.d 0 2) (by simp) with h20720 | h20720
                              · rcases p20714_3 (m.d 0 3) (by simp) with h20721 | h20721
                                · rcases p20714_3 (m.d 0 4) (by simp) with h20722 | h20722
                                  · rcases p20714_3 (m.d 0 5) (by simp) with h20723 | h20723
                                    · linarith only [h20697, h20723, hlam]
                                    · rcases h2bigk with h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c | h20725c
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h0, hlam, p20725_1]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h0, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20725_1]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        rcases p20725_3 (m.d 0 2) (by simp) with h20729 | h20729
                                        · rcases p20725_3 (m.d 1 2) (by simp) with h20730 | h20730
                                          · rcases p20725_3 (m.d 2 3) (by simp) with h20731 | h20731
                                            · linarith only [h20698, h20731, hlam]
                                            · linarith only [h20710, h20731, hlam]
                                          · linarith only [h20705, h20730, hlam]
                                        · linarith only [h20729, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        rcases p20725_3 (m.d 0 2) (by simp) with h20736 | h20736
                                        · rcases p20725_3 (m.d 1 2) (by simp) with h20737 | h20737
                                          · rcases p20725_3 (m.d 2 3) (by simp) with h20738 | h20738
                                            · linarith only [h20698, h20738, hlam]
                                            · linarith only [h20711, h20738, hlam]
                                          · linarith only [h20706, h20737, hlam]
                                        · linarith only [h20736, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h0, h20697, h20706, h20711, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20714_1, p20725_1]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20725_1]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        rcases p20725_3 (m.d 0 2) (by simp) with h20746 | h20746
                                        · linarith only [h0, h20746, hlam]
                                        · linarith only [h20699, h20746, hlam]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h18443, h20697, h20704, h20706, h20707, hlam, p20714_1, p20725_2]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20698, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20704, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20698, h20710, h20713, hc02, hc45, hlam, hphi, ht0b, ht5b, p20725_1]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        rcases p20725_3 (m.d 0 2) (by simp) with h20754 | h20754
                                        · rcases p20725_3 (m.d 1 2) (by simp) with h20755 | h20755
                                          · rcases p20725_3 (m.d 2 3) (by simp) with h20756 | h20756
                                            · rcases p20725_3 (m.d 2 4) (by simp) with h20757 | h20757
                                              · linarith only [h20710, h20757, hlam]
                                              · linarith only [h20712, h20757, hlam]
                                            · linarith only [h20711, h20756, hlam]
                                          · linarith only [h20706, h20755, hlam]
                                        · linarith only [h20700, h20754, hlam]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20699, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20705, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20710, hlam, p20725_1]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        rcases p20725_3 (m.d 0 2) (by simp) with h20767 | h20767
                                        · rcases p20725_3 (m.d 1 2) (by simp) with h20768 | h20768
                                          · rcases p20725_3 (m.d 2 3) (by simp) with h20769 | h20769
                                            · rcases p20725_3 (m.d 2 4) (by simp) with h20770 | h20770
                                              · rcases p20725_3 (m.d 2 5) (by simp) with h20771 | h20771
                                                · linarith only [h20712, h20771, hlam]
                                                · rcases h3bigk with h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c | h20773c
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h15532, hlam, p20773_1]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h0, h20698, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20773_1]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    rcases p20773_3 (m.d 0 3) (by simp) with h20777 | h20777
                                                    · rcases p20773_3 (m.d 1 3) (by simp) with h20778 | h20778
                                                      · rcases p20773_3 (m.d 2 3) (by simp) with h20779 | h20779
                                                        · linarith only [h20698, h20779, hlam]
                                                        · linarith only [h20710, h20779, hlam]
                                                      · linarith only [h20707, h20778, hlam]
                                                    · linarith only [h20777, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    rcases p20773_3 (m.d 0 3) (by simp) with h20784 | h20784
                                                    · rcases p20773_3 (m.d 1 3) (by simp) with h20785 | h20785
                                                      · rcases p20773_3 (m.d 2 3) (by simp) with h20786 | h20786
                                                        · linarith only [h20698, h20786, hlam]
                                                        · linarith only [h20711, h20786, hlam]
                                                      · linarith only [h20708, h20785, hlam]
                                                    · linarith only [h20784, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h15532, h20697, h20704, h20706, h20711, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20714_1, p20773_1]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20704, h20710, h20711, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20725_1, p20773_1]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    rcases p20773_3 (m.d 0 3) (by simp) with h20794 | h20794
                                                    · linarith only [h15532, h20794, hlam]
                                                    · linarith only [h20701, h20794, hlam]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h15532, h20697, h20706, h20711, hlam, p20714_1, p20773_2]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20698, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20704, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h0, h20698, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20773_1]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    rcases p20773_3 (m.d 0 3) (by simp) with h20802 | h20802
                                                    · rcases p20773_3 (m.d 1 3) (by simp) with h20803 | h20803
                                                      · rcases p20773_3 (m.d 2 3) (by simp) with h20804 | h20804
                                                        · rcases p20773_3 (m.d 3 4) (by simp) with h20805 | h20805
                                                          · linarith only [h20710, h20805, hlam]
                                                          · linarith only [h20713, h20805, hlam]
                                                        · linarith only [h20804, hlam, p20773_0]
                                                      · linarith only [h20708, h20803, hlam]
                                                    · linarith only [h20702, h20802, hlam]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20701, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20707, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20710, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h0, h20698, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20773_1]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20702, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20708, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20711, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [h20713, hlam, p20773_0]
                                                  · have p20773_0 := h20773c.1
                                                    have p20773_1 := h20773c.2.1
                                                    have p20773_2 := h20773c.2.2.1
                                                    have p20773_3 := h20773c.2.2.2
                                                    linarith only [hlam, p20773_0]
                                              · linarith only [h20712, h20770, hlam]
                                            · linarith only [h20711, h20769, hlam]
                                          · linarith only [h20706, h20768, hlam]
                                        · linarith only [h20700, h20767, hlam]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20700, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20706, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20711, hlam, p20725_1]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [h20712, hlam, p20725_0]
                                      · have p20725_0 := h20725c.1
                                        have p20725_1 := h20725c.2.1
                                        have p20725_2 := h20725c.2.2.1
                                        have p20725_3 := h20725c.2.2.2
                                        linarith only [hlam, p20725_0]
                                  · linarith only [h20703, h20722, hlam]
                                · linarith only [h20702, h20721, hlam]
                              · linarith only [h20700, h20720, hlam]
                            · linarith only [h20697, h20719, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20834 | h20834
                            · linarith only [h0, h20834, hlam]
                            · rcases p20714_3 (m.d 0 2) (by simp) with h20836 | h20836
                              · rcases p20714_3 (m.d 0 3) (by simp) with h20837 | h20837
                                · linarith only [h20698, h20837, hlam]
                                · linarith only [h15532, h20837, hlam]
                              · linarith only [h0, h20836, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h0, h20698, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20714_1]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20843 | h20843
                            · linarith only [h0, h20843, hlam]
                            · rcases p20714_3 (m.d 0 2) (by simp) with h20845 | h20845
                              · rcases p20714_3 (m.d 0 3) (by simp) with h20846 | h20846
                                · linarith only [h20698, h20846, hlam]
                                · linarith only [h20701, h20846, hlam]
                              · linarith only [h20699, h20845, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20850 | h20850
                            · linarith only [h0, h20850, hlam]
                            · linarith only [h20697, h20850, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20853 | h20853
                            · linarith only [h15532, h20853, hlam]
                            · rcases p20714_3 (m.d 0 2) (by simp) with h20855 | h20855
                              · rcases p20714_3 (m.d 0 3) (by simp) with h20856 | h20856
                                · rcases p20714_3 (m.d 0 4) (by simp) with h20857 | h20857
                                  · linarith only [h20701, h20857, hlam]
                                  · linarith only [h18443, h20857, hlam]
                                · linarith only [h15532, h20856, hlam]
                              · linarith only [h0, h20855, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h20698, hlam, p20714_1]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20864 | h20864
                            · linarith only [h15532, h20864, hlam]
                            · rcases p20714_3 (m.d 0 2) (by simp) with h20866 | h20866
                              · rcases p20714_3 (m.d 0 3) (by simp) with h20867 | h20867
                                · rcases p20714_3 (m.d 0 4) (by simp) with h20868 | h20868
                                  · linarith only [h20701, h20868, hlam]
                                  · rcases p20714_3 (m.d 0 5) (by simp) with h20870 | h20870
                                    · linarith only [h20702, h20870, hlam]
                                    · rcases h2bigk with h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c | h20872c
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h0, hlam, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h0, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        rcases p20872_3 (m.d 0 2) (by simp) with h20876 | h20876
                                        · rcases p20872_3 (m.d 1 2) (by simp) with h20877 | h20877
                                          · rcases p20872_3 (m.d 2 3) (by simp) with h20878 | h20878
                                            · linarith only [h20698, h20878, hlam]
                                            · linarith only [h20710, h20878, hlam]
                                          · linarith only [h20705, h20877, hlam]
                                        · linarith only [h20876, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h18443, h20697, h20698, h20706, hlam, p20714_1, p20872_2]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h18443, h20698, hc01, hc12, hlam, hphi, p20714_1, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        rcases p20872_3 (m.d 0 2) (by simp) with h20887 | h20887
                                        · linarith only [h0, h20887, hlam]
                                        · linarith only [h20699, h20887, hlam]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h0, h18443, h20697, h20698, h20706, hlam, p20714_1, p20872_2]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20698, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20704, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20698, h20710, h20713, hc02, hc45, hlam, hphi, ht0b, ht5b, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        rcases p20872_3 (m.d 0 2) (by simp) with h20895 | h20895
                                        · rcases p20872_3 (m.d 1 2) (by simp) with h20896 | h20896
                                          · rcases p20872_3 (m.d 2 3) (by simp) with h20897 | h20897
                                            · rcases p20872_3 (m.d 2 4) (by simp) with h20898 | h20898
                                              · linarith only [h20710, h20898, hlam]
                                              · linarith only [h20712, h20898, hlam]
                                            · linarith only [h20711, h20897, hlam]
                                          · linarith only [h20706, h20896, hlam]
                                        · linarith only [h20700, h20895, hlam]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20699, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20705, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20710, hlam, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20699, h20711, h20713, hc03, hc45, hlam, hphi, ht0b, ht5b, p20714_1, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20700, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20706, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20711, hlam, p20872_1]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [h20712, hlam, p20872_0]
                                      · have p20872_0 := h20872c.1
                                        have p20872_1 := h20872c.2.1
                                        have p20872_2 := h20872c.2.2.1
                                        have p20872_3 := h20872c.2.2.2
                                        linarith only [hlam, p20872_0]
                                · linarith only [h20701, h20867, hlam]
                              · linarith only [h20699, h20866, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20916 | h20916
                            · linarith only [h15532, h20916, hlam]
                            · linarith only [h20697, h20916, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h20919 | h20919
                            · linarith only [h18443, h20919, hlam]
                            · rcases p20714_3 (m.d 0 2) (by simp) with h20921 | h20921
                              · rcases p20714_3 (m.d 0 3) (by simp) with h20922 | h20922
                                · rcases p20714_3 (m.d 0 4) (by simp) with h20923 | h20923
                                  · rcases p20714_3 (m.d 0 5) (by simp) with h20924 | h20924
                                    · linarith only [h20703, h20924, hlam]
                                    · rcases h2bigk with h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c | h20926c
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h0, hlam, p20926_1]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h0, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20926_1]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        rcases p20926_3 (m.d 0 2) (by simp) with h20930 | h20930
                                        · rcases p20926_3 (m.d 1 2) (by simp) with h20931 | h20931
                                          · rcases p20926_3 (m.d 2 3) (by simp) with h20932 | h20932
                                            · linarith only [h20698, h20932, hlam]
                                            · linarith only [h20710, h20932, hlam]
                                          · linarith only [h20705, h20931, hlam]
                                        · linarith only [h20930, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20697, h20699, h20706, hlam, p20714_1, p20926_2]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20698, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20926_1]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20926_1]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        rcases p20926_3 (m.d 0 2) (by simp) with h20941 | h20941
                                        · linarith only [h0, h20941, hlam]
                                        · linarith only [h20699, h20941, hlam]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h0, h20697, h20698, h20701, h20706, hlam, p20714_1, p20926_2]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20698, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20704, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20698, h20710, h20713, hc02, hc45, hlam, hphi, ht0b, ht5b, p20926_1]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        rcases p20926_3 (m.d 0 2) (by simp) with h20949 | h20949
                                        · rcases p20926_3 (m.d 1 2) (by simp) with h20950 | h20950
                                          · rcases p20926_3 (m.d 2 3) (by simp) with h20951 | h20951
                                            · rcases p20926_3 (m.d 2 4) (by simp) with h20952 | h20952
                                              · linarith only [h20710, h20952, hlam]
                                              · linarith only [h20712, h20952, hlam]
                                            · linarith only [h20711, h20951, hlam]
                                          · linarith only [h20706, h20950, hlam]
                                        · linarith only [h20700, h20949, hlam]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20699, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20705, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20710, hlam, p20926_1]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        rcases p20926_3 (m.d 0 2) (by simp) with h20962 | h20962
                                        · rcases p20926_3 (m.d 1 2) (by simp) with h20963 | h20963
                                          · rcases p20926_3 (m.d 2 3) (by simp) with h20964 | h20964
                                            · rcases p20926_3 (m.d 2 4) (by simp) with h20965 | h20965
                                              · rcases p20926_3 (m.d 2 5) (by simp) with h20966 | h20966
                                                · linarith only [h20712, h20966, hlam]
                                                · rcases h3bigk with h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c | h20968c
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h15532, hlam, p20968_1]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h15532, h20704, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20968_1]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    rcases p20968_3 (m.d 0 3) (by simp) with h20972 | h20972
                                                    · rcases p20968_3 (m.d 1 3) (by simp) with h20973 | h20973
                                                      · rcases p20968_3 (m.d 2 3) (by simp) with h20974 | h20974
                                                        · linarith only [h20698, h20974, hlam]
                                                        · linarith only [h20710, h20974, hlam]
                                                      · linarith only [h20707, h20973, hlam]
                                                    · linarith only [h20972, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20697, h20701, h20706, h20711, hlam, p20714_1, p20968_2]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20698, h20704, h20710, h20711, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20926_1, p20968_1]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20704, h20710, h20711, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20926_1, p20968_1]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    rcases p20968_3 (m.d 0 3) (by simp) with h20983 | h20983
                                                    · linarith only [h15532, h20983, hlam]
                                                    · linarith only [h20701, h20983, hlam]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h15532, h20697, h20701, h20706, h20711, hlam, p20714_1, p20968_2]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20698, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20704, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h0, h20698, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20968_1]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    rcases p20968_3 (m.d 0 3) (by simp) with h20991 | h20991
                                                    · rcases p20968_3 (m.d 1 3) (by simp) with h20992 | h20992
                                                      · rcases p20968_3 (m.d 2 3) (by simp) with h20993 | h20993
                                                        · rcases p20968_3 (m.d 3 4) (by simp) with h20994 | h20994
                                                          · linarith only [h20710, h20994, hlam]
                                                          · linarith only [h20713, h20994, hlam]
                                                        · linarith only [h20993, hlam, p20968_0]
                                                      · linarith only [h20708, h20992, hlam]
                                                    · linarith only [h20702, h20991, hlam]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20701, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20707, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20710, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h0, h20698, h20710, h20713, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p20968_1]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20702, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20708, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20711, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [h20713, hlam, p20968_0]
                                                  · have p20968_0 := h20968c.1
                                                    have p20968_1 := h20968c.2.1
                                                    have p20968_2 := h20968c.2.2.1
                                                    have p20968_3 := h20968c.2.2.2
                                                    linarith only [hlam, p20968_0]
                                              · linarith only [h20712, h20965, hlam]
                                            · linarith only [h20711, h20964, hlam]
                                          · linarith only [h20706, h20963, hlam]
                                        · linarith only [h20700, h20962, hlam]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20700, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20706, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20711, hlam, p20926_1]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [h20712, hlam, p20926_0]
                                      · have p20926_0 := h20926c.1
                                        have p20926_1 := h20926c.2.1
                                        have p20926_2 := h20926c.2.2.1
                                        have p20926_3 := h20926c.2.2.2
                                        linarith only [hlam, p20926_0]
                                  · linarith only [h18443, h20923, hlam]
                                · linarith only [h15532, h20922, hlam]
                              · linarith only [h0, h20921, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h20699, hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h20701, hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            rcases p20714_3 (m.d 0 1) (by simp) with h21025 | h21025
                            · linarith only [h18443, h21025, hlam]
                            · linarith only [h20697, h21025, hlam]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h20697, hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h20700, hlam, p20714_1]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h20702, hlam, p20714_0]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [h20703, hlam, p20714_1]
                          · have p20714_0 := h20714c.1
                            have p20714_1 := h20714c.2.1
                            have p20714_2 := h20714c.2.2.1
                            have p20714_3 := h20714c.2.2.2
                            linarith only [hlam, p20714_0]
                        · rcases h0bigk with h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c | h21033c
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h0, hlam, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h15532, hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h18443, hlam, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h0, h20697, h20706, h20712, h20713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h0, h20697, h20706, h20712, h20713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h0, h15532, h20697, h20706, h20712, h20713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h0, h18443, h20697, h20706, h20712, h20713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            rcases p21033_3 (m.d 0 1) (by simp) with h21043 | h21043
                            · linarith only [h0, h21043, hlam]
                            · linarith only [h20697, h21043, hlam]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20697, h20706, h20712, h20713, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20698, hlam, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h15532, h18443, h20697, h20704, h20706, h20712, h20713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            rcases p21033_3 (m.d 0 1) (by simp) with h21050 | h21050
                            · linarith only [h15532, h21050, hlam]
                            · linarith only [h20697, h21050, hlam]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20697, h20706, h20712, h20713, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20699, hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20701, hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            rcases p21033_3 (m.d 0 1) (by simp) with h21057 | h21057
                            · linarith only [h18443, h21057, hlam]
                            · linarith only [h20697, h21057, hlam]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20697, hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20700, hlam, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20702, hlam, p21033_0]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [h20703, hlam, p21033_1]
                          · have p21033_0 := h21033c.1
                            have p21033_1 := h21033c.2.1
                            have p21033_2 := h21033c.2.2.1
                            have p21033_3 := h21033c.2.2.2
                            linarith only [hlam, p21033_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21065 | h21065
                        · linarith only [h20710, h20712, h21065, hlam]
                        · rcases h0bigk with h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c | h21067c
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h0, hlam, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h15532, hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h18443, hlam, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h15532, h20703, h20704, h20710, h20712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h0, h20697, h20709, h20710, h20712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h0, h20701, h20703, h20710, h20712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h0, h20703, h20710, h20712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            rcases p21067_3 (m.d 0 1) (by simp) with h21077 | h21077
                            · linarith only [h0, h21077, hlam]
                            · linarith only [h20697, h21077, hlam]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20697, h20709, h20710, h20712, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20698, hlam, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h15532, h18443, h20697, h20704, h20709, h20710, h20712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            rcases p21067_3 (m.d 0 1) (by simp) with h21084 | h21084
                            · linarith only [h15532, h21084, hlam]
                            · linarith only [h20697, h21084, hlam]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20697, h20709, h20710, h20712, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20699, hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20701, hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            rcases p21067_3 (m.d 0 1) (by simp) with h21091 | h21091
                            · linarith only [h18443, h21091, hlam]
                            · linarith only [h20697, h21091, hlam]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20697, hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20700, hlam, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20702, hlam, p21067_0]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [h20703, hlam, p21067_1]
                          · have p21067_0 := h21067c.1
                            have p21067_1 := h21067c.2.1
                            have p21067_2 := h21067c.2.2.1
                            have p21067_3 := h21067c.2.2.2
                            linarith only [hlam, p21067_0]
                    · linarith only [h0, h20697, h20708, h20710, h20711, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21100 | h21100
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21101 | h21101
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21102 | h21102
                        · rcases h0bigk with h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c | h21103c
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h0, hlam, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h15532, hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h18443, hlam, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            rcases p21103_3 (m.d 0 1) (by simp) with h21108 | h21108
                            · rcases p21103_3 (m.d 0 2) (by simp) with h21109 | h21109
                              · rcases p21103_3 (m.d 0 3) (by simp) with h21110 | h21110
                                · rcases p21103_3 (m.d 0 4) (by simp) with h21111 | h21111
                                  · rcases p21103_3 (m.d 0 5) (by simp) with h21112 | h21112
                                    · linarith only [h20697, h21112, hlam]
                                    · rcases h2bigk with h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c | h21114c
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h0, hlam, p21114_1]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        rcases p21114_3 (m.d 0 2) (by simp) with h21117 | h21117
                                        · rcases p21114_3 (m.d 1 2) (by simp) with h21118 | h21118
                                          · rcases p21114_3 (m.d 2 3) (by simp) with h21119 | h21119
                                            · linarith only [h21119, hlam, p21114_0]
                                            · rcases p21114_3 (m.d 2 4) (by simp) with h21121 | h21121
                                              · linarith only [h20699, h21121, hlam]
                                              · linarith only [h20710, h21121, hlam]
                                          · linarith only [h20704, h21118, hlam]
                                        · linarith only [h21117, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        rcases p21114_3 (m.d 0 2) (by simp) with h21126 | h21126
                                        · rcases p21114_3 (m.d 1 2) (by simp) with h21127 | h21127
                                          · rcases p21114_3 (m.d 2 3) (by simp) with h21128 | h21128
                                            · linarith only [h20698, h21128, hlam]
                                            · rcases p21114_3 (m.d 2 4) (by simp) with h21130 | h21130
                                              · linarith only [h21130, hlam, p21114_0]
                                              · rcases p21114_3 (m.d 2 5) (by simp) with h21132 | h21132
                                                · linarith only [h20700, h21132, hlam]
                                                · rcases h3bigk with h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c | h21134c
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h15532, hlam, p21134_1]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    rcases p21134_3 (m.d 0 3) (by simp) with h21137 | h21137
                                                    · rcases p21134_3 (m.d 1 3) (by simp) with h21138 | h21138
                                                      · rcases p21134_3 (m.d 2 3) (by simp) with h21139 | h21139
                                                        · linarith only [h20698, h21139, hlam]
                                                        · rcases p21134_3 (m.d 3 4) (by simp) with h21141 | h21141
                                                          · linarith only [h20701, h21141, hlam]
                                                          · linarith only [h20710, h21141, hlam]
                                                      · linarith only [h20704, h21138, hlam]
                                                    · linarith only [h20698, h21137, hlam]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h15532, h20704, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21134_1]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20701, h20710, h21100, hlam, p21134_2]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h15532, h20704, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p21103_1, p21134_1]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    rcases p21134_3 (m.d 0 3) (by simp) with h21150 | h21150
                                                    · linarith only [h15532, h21150, hlam]
                                                    · linarith only [h20698, h21150, hlam]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20704, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21134_1]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h15532, h20697, h20706, h21100, hlam, p21103_1, p21134_2]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20698, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20704, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20710, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20701, h20710, h21102, hc03, hc45, hlam, hphi, ht0b, ht5b, p21134_1]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20701, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20707, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h0, h20698, h20701, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21134_1]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    rcases p21134_3 (m.d 0 3) (by simp) with h21164 | h21164
                                                    · rcases p21134_3 (m.d 1 3) (by simp) with h21165 | h21165
                                                      · rcases p21134_3 (m.d 2 3) (by simp) with h21166 | h21166
                                                        · linarith only [h20710, h21166, hlam]
                                                        · linarith only [h21100, h21166, hlam]
                                                      · linarith only [h20708, h21165, hlam]
                                                    · linarith only [h20702, h21164, hlam]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20702, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h20708, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h21100, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [h21102, hlam, p21134_0]
                                                  · have p21134_0 := h21134c.1
                                                    have p21134_1 := h21134c.2.1
                                                    have p21134_2 := h21134c.2.2.1
                                                    have p21134_3 := h21134c.2.2.2
                                                    linarith only [hlam, p21134_0]
                                          · linarith only [h20705, h21127, hlam]
                                        · linarith only [h21126, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        rcases p21114_3 (m.d 0 2) (by simp) with h21178 | h21178
                                        · rcases p21114_3 (m.d 1 2) (by simp) with h21179 | h21179
                                          · rcases p21114_3 (m.d 2 3) (by simp) with h21180 | h21180
                                            · linarith only [h20698, h21180, hlam]
                                            · linarith only [h21100, h21180, hlam]
                                          · linarith only [h20706, h21179, hlam]
                                        · linarith only [h21178, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p21103_1, p21114_1]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        rcases p21114_3 (m.d 0 2) (by simp) with h21187 | h21187
                                        · linarith only [h0, h21187, hlam]
                                        · linarith only [h20698, h21187, hlam]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        rcases p21114_3 (m.d 0 2) (by simp) with h21190 | h21190
                                        · linarith only [h0, h21190, hlam]
                                        · linarith only [h20699, h21190, hlam]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h0, h20697, h20706, hlam, p21103_1, p21114_2]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20698, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20704, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20710, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20698, h20701, h20710, h21100, h21102, hc02, hc45, hlam, hphi, ht0b, ht5b, p21114_1]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20699, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20705, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h0, h20698, h20701, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21114_1]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        rcases p21114_3 (m.d 0 2) (by simp) with h21203 | h21203
                                        · rcases p21114_3 (m.d 1 2) (by simp) with h21204 | h21204
                                          · rcases p21114_3 (m.d 2 3) (by simp) with h21205 | h21205
                                            · linarith only [h20710, h21205, hlam]
                                            · linarith only [h21100, h21205, hlam]
                                          · linarith only [h20706, h21204, hlam]
                                        · linarith only [h20700, h21203, hlam]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20700, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h20706, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h21100, hlam, p21114_1]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [h21101, hlam, p21114_0]
                                      · have p21114_0 := h21114c.1
                                        have p21114_1 := h21114c.2.1
                                        have p21114_2 := h21114c.2.2.1
                                        have p21114_3 := h21114c.2.2.2
                                        linarith only [hlam, p21114_0]
                                  · linarith only [h20703, h21111, hlam]
                                · linarith only [h20702, h21110, hlam]
                              · linarith only [h20700, h21109, hlam]
                            · linarith only [h20697, h21108, hlam]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            rcases p21103_3 (m.d 0 1) (by simp) with h21219 | h21219
                            · linarith only [h0, h21219, hlam]
                            · rcases p21103_3 (m.d 0 2) (by simp) with h21221 | h21221
                              · rcases p21103_3 (m.d 0 3) (by simp) with h21222 | h21222
                                · linarith only [h20698, h21222, hlam]
                                · linarith only [h15532, h21222, hlam]
                              · linarith only [h0, h21221, hlam]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h0, h20701, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h0, h20701, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            rcases p21103_3 (m.d 0 1) (by simp) with h21229 | h21229
                            · linarith only [h0, h21229, hlam]
                            · linarith only [h20697, h21229, hlam]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            rcases p21103_3 (m.d 0 1) (by simp) with h21232 | h21232
                            · linarith only [h15532, h21232, hlam]
                            · rcases p21103_3 (m.d 0 2) (by simp) with h21234 | h21234
                              · rcases p21103_3 (m.d 0 3) (by simp) with h21235 | h21235
                                · rcases p21103_3 (m.d 0 4) (by simp) with h21236 | h21236
                                  · linarith only [h20701, h21236, hlam]
                                  · linarith only [h18443, h21236, hlam]
                                · linarith only [h15532, h21235, hlam]
                              · linarith only [h0, h21234, hlam]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20698, hlam, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20701, h20710, h21100, h21102, hc03, hc45, hlam, hphi, ht0b, ht5b, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            rcases p21103_3 (m.d 0 1) (by simp) with h21244 | h21244
                            · linarith only [h15532, h21244, hlam]
                            · linarith only [h20697, h21244, hlam]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            rcases p21103_3 (m.d 0 1) (by simp) with h21247 | h21247
                            · linarith only [h18443, h21247, hlam]
                            · rcases p21103_3 (m.d 0 2) (by simp) with h21249 | h21249
                              · rcases p21103_3 (m.d 0 3) (by simp) with h21250 | h21250
                                · rcases p21103_3 (m.d 0 4) (by simp) with h21251 | h21251
                                  · rcases p21103_3 (m.d 0 5) (by simp) with h21252 | h21252
                                    · linarith only [h20703, h21252, hlam]
                                    · rcases h2bigk with h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c | h21254c
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h0, hlam, p21254_1]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        rcases p21254_3 (m.d 0 2) (by simp) with h21257 | h21257
                                        · rcases p21254_3 (m.d 1 2) (by simp) with h21258 | h21258
                                          · rcases p21254_3 (m.d 2 3) (by simp) with h21259 | h21259
                                            · linarith only [h21259, hlam, p21254_0]
                                            · rcases p21254_3 (m.d 2 4) (by simp) with h21261 | h21261
                                              · linarith only [h20699, h21261, hlam]
                                              · linarith only [h20710, h21261, hlam]
                                          · linarith only [h20704, h21258, hlam]
                                        · linarith only [h21257, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        rcases p21254_3 (m.d 0 2) (by simp) with h21266 | h21266
                                        · rcases p21254_3 (m.d 1 2) (by simp) with h21267 | h21267
                                          · rcases p21254_3 (m.d 2 3) (by simp) with h21268 | h21268
                                            · linarith only [h20698, h21268, hlam]
                                            · rcases p21254_3 (m.d 2 4) (by simp) with h21270 | h21270
                                              · linarith only [h21270, hlam, p21254_0]
                                              · rcases p21254_3 (m.d 2 5) (by simp) with h21272 | h21272
                                                · linarith only [h20700, h21272, hlam]
                                                · rcases h3bigk with h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c | h21274c
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h15532, hlam, p21274_1]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    rcases p21274_3 (m.d 0 3) (by simp) with h21277 | h21277
                                                    · rcases p21274_3 (m.d 1 3) (by simp) with h21278 | h21278
                                                      · rcases p21274_3 (m.d 2 3) (by simp) with h21279 | h21279
                                                        · linarith only [h20698, h21279, hlam]
                                                        · rcases p21274_3 (m.d 3 4) (by simp) with h21281 | h21281
                                                          · linarith only [h20701, h21281, hlam]
                                                          · linarith only [h20710, h21281, hlam]
                                                      · linarith only [h20704, h21278, hlam]
                                                    · linarith only [h20698, h21277, hlam]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h0, h20698, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21274_1]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20701, h20710, h21100, hlam, p21274_2]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20701, h20704, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21274_1]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    rcases p21274_3 (m.d 0 3) (by simp) with h21290 | h21290
                                                    · linarith only [h15532, h21290, hlam]
                                                    · linarith only [h20698, h21290, hlam]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20704, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21274_1]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h15532, h20697, h20701, h20706, h21100, hlam, p21103_1, p21274_2]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20698, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20704, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20710, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20701, h20710, h21102, hc03, hc45, hlam, hphi, ht0b, ht5b, p21274_1]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20701, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20707, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h0, h20698, h20701, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21274_1]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    rcases p21274_3 (m.d 0 3) (by simp) with h21304 | h21304
                                                    · rcases p21274_3 (m.d 1 3) (by simp) with h21305 | h21305
                                                      · rcases p21274_3 (m.d 2 3) (by simp) with h21306 | h21306
                                                        · linarith only [h20710, h21306, hlam]
                                                        · linarith only [h21100, h21306, hlam]
                                                      · linarith only [h20708, h21305, hlam]
                                                    · linarith only [h20702, h21304, hlam]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20702, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h20708, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h21100, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [h21102, hlam, p21274_0]
                                                  · have p21274_0 := h21274c.1
                                                    have p21274_1 := h21274c.2.1
                                                    have p21274_2 := h21274c.2.2.1
                                                    have p21274_3 := h21274c.2.2.2
                                                    linarith only [hlam, p21274_0]
                                          · linarith only [h20705, h21267, hlam]
                                        · linarith only [h21266, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20697, h20699, h20706, hlam, p21103_1, p21254_2]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20698, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21254_1]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        rcases p21254_3 (m.d 0 2) (by simp) with h21321 | h21321
                                        · linarith only [h0, h21321, hlam]
                                        · linarith only [h20698, h21321, hlam]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        rcases p21254_3 (m.d 0 2) (by simp) with h21324 | h21324
                                        · linarith only [h0, h21324, hlam]
                                        · linarith only [h20699, h21324, hlam]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h0, h20697, h20698, h20701, h20706, hlam, p21103_1, p21254_2]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20698, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20704, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20710, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h0, h20698, h20701, h20710, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p21254_1]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20699, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20705, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h0, h20698, h20701, h20710, h21100, h21102, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21254_1]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        rcases p21254_3 (m.d 0 2) (by simp) with h21337 | h21337
                                        · rcases p21254_3 (m.d 1 2) (by simp) with h21338 | h21338
                                          · rcases p21254_3 (m.d 2 3) (by simp) with h21339 | h21339
                                            · linarith only [h20710, h21339, hlam]
                                            · linarith only [h21100, h21339, hlam]
                                          · linarith only [h20706, h21338, hlam]
                                        · linarith only [h20700, h21337, hlam]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20700, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h20706, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h21100, hlam, p21254_1]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [h21101, hlam, p21254_0]
                                      · have p21254_0 := h21254c.1
                                        have p21254_1 := h21254c.2.1
                                        have p21254_2 := h21254c.2.2.1
                                        have p21254_3 := h21254c.2.2.2
                                        linarith only [hlam, p21254_0]
                                  · linarith only [h18443, h21251, hlam]
                                · linarith only [h15532, h21250, hlam]
                              · linarith only [h0, h21249, hlam]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20699, hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20701, hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            rcases p21103_3 (m.d 0 1) (by simp) with h21355 | h21355
                            · linarith only [h18443, h21355, hlam]
                            · linarith only [h20697, h21355, hlam]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20697, hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20700, hlam, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20702, hlam, p21103_0]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [h20703, hlam, p21103_1]
                          · have p21103_0 := h21103c.1
                            have p21103_1 := h21103c.2.1
                            have p21103_2 := h21103c.2.2.1
                            have p21103_3 := h21103c.2.2.2
                            linarith only [hlam, p21103_0]
                        · linarith only [h18443, h20697, h20704, h20707, h20709, h20710, h21102, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h18443, h20697, h20704, h20707, h20709, h20710, h21100, h21101, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21365 | h21365
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21366 | h21366
                        · rcases h0bigk with h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c | h21367c
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h0, hlam, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h15532, hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h18443, hlam, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h18443, h20697, h20704, h20707, h20708, h21100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h0, h20697, h20708, h21100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h0, h18443, h20697, h20701, h20708, h21100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h0, h18443, h20697, h20708, h21100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            rcases p21367_3 (m.d 0 1) (by simp) with h21377 | h21377
                            · linarith only [h0, h21377, hlam]
                            · linarith only [h20697, h21377, hlam]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20697, h20708, h21100, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20698, hlam, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h15532, h18443, h20697, h20704, h20708, h21100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            rcases p21367_3 (m.d 0 1) (by simp) with h21384 | h21384
                            · linarith only [h15532, h21384, hlam]
                            · linarith only [h20697, h21384, hlam]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20697, h20708, h21100, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20699, hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20701, hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            rcases p21367_3 (m.d 0 1) (by simp) with h21391 | h21391
                            · linarith only [h18443, h21391, hlam]
                            · linarith only [h20697, h21391, hlam]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20697, hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20700, hlam, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20702, hlam, p21367_0]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [h20703, hlam, p21367_1]
                          · have p21367_0 := h21367c.1
                            have p21367_1 := h21367c.2.1
                            have p21367_2 := h21367c.2.2.1
                            have p21367_3 := h21367c.2.2.2
                            linarith only [hlam, p21367_0]
                        · linarith only [h0, h20699, h20710, h21365, h21366, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21400 | h21400
                        · rcases h0bigk with h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c | h21401c
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h0, hlam, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h15532, hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h18443, hlam, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h0, h20697, h20708, h20710, h21365, h21400, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h0, h20697, h20708, h20710, h21365, h21400, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h0, h15532, h20697, h20708, h20710, h21365, h21400, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h0, h18443, h20697, h20708, h20710, h21365, h21400, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            rcases p21401_3 (m.d 0 1) (by simp) with h21411 | h21411
                            · linarith only [h0, h21411, hlam]
                            · linarith only [h20697, h21411, hlam]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20697, h20708, h20710, h21365, h21400, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20698, hlam, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h15532, h18443, h20697, h20704, h20708, h20710, h21365, h21400, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            rcases p21401_3 (m.d 0 1) (by simp) with h21418 | h21418
                            · linarith only [h15532, h21418, hlam]
                            · linarith only [h20697, h21418, hlam]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20697, h20708, h20710, h21365, h21400, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20699, hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20701, hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            rcases p21401_3 (m.d 0 1) (by simp) with h21425 | h21425
                            · linarith only [h18443, h21425, hlam]
                            · linarith only [h20697, h21425, hlam]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20697, hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20700, hlam, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20702, hlam, p21401_0]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [h20703, hlam, p21401_1]
                          · have p21401_0 := h21401c.1
                            have p21401_1 := h21401c.2.1
                            have p21401_2 := h21401c.2.2.1
                            have p21401_3 := h21401c.2.2.2
                            linarith only [hlam, p21401_0]
                        · linarith only [h0, h20697, h20709, h20710, h21400, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h18443, h20703, h20709, hlam]
              · linarith only [h15532, h20702, h20708, hlam]
            · linarith only [h15532, h20701, h20707, hlam]
          · linarith only [h0, h20700, h20706, hlam]
        · linarith only [h0, h20699, h20705, hlam]
      · linarith only [h0, h20698, h20704, hlam]
    · linarith only [h18443, h20697, h20703, hlam]
  · linarith only [h18443, h20697, h20701, h20702, hlam]

end R2N4
