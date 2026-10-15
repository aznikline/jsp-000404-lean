import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19727 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h19728 | h19728
  · rcases m.htr 0 2 5 (by decide) (by decide) with h19729 | h19729
    · rcases m.htr 0 3 4 (by decide) (by decide) with h19730 | h19730
      · rcases m.htr 0 3 5 (by decide) (by decide) with h19731 | h19731
        · rcases m.htr 0 4 5 (by decide) (by decide) with h19732 | h19732
          · linarith only [h18443, h18444, h19732, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19734 | h19734
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19735 | h19735
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19736 | h19736
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19737 | h19737
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19738 | h19738
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19739 | h19739
                      · linarith only [h18443, h18444, h19732, h19739, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19741 | h19741
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19742 | h19742
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19743 | h19743
                            · linarith only [h18443, h18444, h19735, h19739, h19743, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19745 | h19745
                              · linarith only [h18444, h19727, h19739, h19741, h19745, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h0bigk with h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c | h19747c
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h0, hlam, p19747_1]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h15532, hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h18444, h19739, hc04, hc45, hlam, hphi, p19747_1]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h18444, hlam, p19747_1]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h19753 | h19753
                                  · linarith only [h0, h19753, hlam]
                                  · rcases p19747_3 (m.d 0 2) (by simp) with h19755 | h19755
                                    · rcases p19747_3 (m.d 0 3) (by simp) with h19756 | h19756
                                      · linarith only [h19727, h19756, hlam]
                                      · linarith only [h15532, h19756, hlam]
                                    · linarith only [h0, h19755, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h19761 | h19761
                                  · linarith only [h0, h19761, hlam]
                                  · rcases p19747_3 (m.d 0 2) (by simp) with h19763 | h19763
                                    · rcases p19747_3 (m.d 0 3) (by simp) with h19764 | h19764
                                      · linarith only [h19727, h19764, hlam]
                                      · rcases p19747_3 (m.d 0 4) (by simp) with h19766 | h19766
                                        · linarith only [h19728, h19766, hlam]
                                        · rcases p19747_3 (m.d 0 5) (by simp) with h19768 | h19768
                                          · linarith only [h19729, h19768, hlam]
                                          · rcases h2bigk with h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c | h19770c
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h0, hlam, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              rcases p19770_3 (m.d 0 2) (by simp) with h19773 | h19773
                                              · rcases p19770_3 (m.d 1 2) (by simp) with h19774 | h19774
                                                · rcases p19770_3 (m.d 2 3) (by simp) with h19775 | h19775
                                                  · linarith only [h19775, hlam, p19770_0]
                                                  · rcases p19770_3 (m.d 2 4) (by simp) with h19777 | h19777
                                                    · linarith only [h19728, h19777, hlam]
                                                    · rcases p19770_3 (m.d 2 5) (by simp) with h19779 | h19779
                                                      · linarith only [h19729, h19779, hlam]
                                                      · rcases h3bigk with h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c | h19781c
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h15532, hlam, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19747_1, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19747_1, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          rcases p19781_3 (m.d 0 3) (by simp) with h19787 | h19787
                                                          · linarith only [h15532, h19787, hlam]
                                                          · rcases p19781_3 (m.d 1 3) (by simp) with h19789 | h19789
                                                            · rcases p19781_3 (m.d 2 3) (by simp) with h19790 | h19790
                                                              · linarith only [h19734, h19790, hlam]
                                                              · rcases p19781_3 (m.d 3 4) (by simp) with h19792 | h19792
                                                                · linarith only [h19737, h19792, hlam]
                                                                · rcases p19781_3 (m.d 3 5) (by simp) with h19794 | h19794
                                                                  · linarith only [h19738, h19794, hlam]
                                                                  · rcases h5bigk with h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c | h19796c
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [hlam, p19796_0]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h18444, hlam, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h0, h19731, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19747_1, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h0, h19731, h19745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19732, hlam, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h18444, h19739, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [hlam, p19796_0]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19739, h19742, h19745, hc34, hc45, hlam, hphi, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19739, h19745, hc34, hc45, hlam, hphi, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19739, hlam, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19729, hlam, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19736, hlam, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [hlam, p19796_0]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h0, h19729, h19745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19743, hlam, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19731, hlam, p19796_0]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19738, hlam, p19796_0]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19742, hlam, p19796_0]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [hlam, p19796_0]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19745, hlam, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc34, hc45, hlam, hphi, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc34, hc45, hlam, hphi, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19742, h19745, hc34, hc45, hlam, hphi, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [h19745, hc34, hc45, hlam, hphi, p19796_1]
                                                                    · have p19796_0 := h19796c.1
                                                                      have p19796_1 := h19796c.2.1
                                                                      have p19796_2 := h19796c.2.2.1
                                                                      have p19796_3 := h19796c.2.2.2
                                                                      linarith only [hlam, p19796_0]
                                                            · linarith only [h15532, h19789, hlam]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          rcases p19781_3 (m.d 0 3) (by simp) with h19824 | h19824
                                                          · linarith only [h15532, h19824, hlam]
                                                          · linarith only [h19727, h19824, hlam]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          rcases p19781_3 (m.d 0 3) (by simp) with h19827 | h19827
                                                          · linarith only [h15532, h19827, hlam]
                                                          · linarith only [h19730, h19827, hlam]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          rcases p19781_3 (m.d 0 3) (by simp) with h19830 | h19830
                                                          · linarith only [h15532, h19830, hlam]
                                                          · linarith only [h19731, h19830, hlam]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19727, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19734, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p19770_1, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h0, h19745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19770_1, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19730, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19737, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19741, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19745, hlam, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19731, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19738, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h19742, hlam, p19781_0]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [h0, h19731, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p19781_1]
                                                        · have p19781_0 := h19781c.1
                                                          have p19781_1 := h19781c.2.1
                                                          have p19781_2 := h19781c.2.2.1
                                                          have p19781_3 := h19781c.2.2.2
                                                          linarith only [hlam, p19781_0]
                                                · linarith only [h19734, h19774, hlam]
                                              · linarith only [h19773, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h15532, h18443, h19735, hlam, p19747_1, p19770_2]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              rcases p19770_3 (m.d 0 2) (by simp) with h19851 | h19851
                                              · rcases p19770_3 (m.d 1 2) (by simp) with h19852 | h19852
                                                · rcases p19770_3 (m.d 2 3) (by simp) with h19853 | h19853
                                                  · linarith only [h19727, h19853, hlam]
                                                  · linarith only [h19742, h19853, hlam]
                                                · linarith only [h19736, h19852, hlam]
                                              · linarith only [h19851, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19727, h19742, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              rcases p19770_3 (m.d 0 2) (by simp) with h19860 | h19860
                                              · linarith only [h0, h19860, hlam]
                                              · linarith only [h19727, h19860, hlam]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h0, h18443, h18444, h19731, h19735, hlam, p19747_1, p19770_2]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              rcases p19770_3 (m.d 0 2) (by simp) with h19864 | h19864
                                              · linarith only [h0, h19864, hlam]
                                              · linarith only [h19729, h19864, hlam]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19727, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19734, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19727, h19741, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p19747_1, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h0, h19727, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19747_1, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19728, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19735, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19741, hlam, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19743, hlam, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19729, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19736, hlam, p19770_0]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h19742, hlam, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [h0, h19729, h19731, h19741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p19770_1]
                                            · have p19770_0 := h19770c.1
                                              have p19770_1 := h19770c.2.1
                                              have p19770_2 := h19770c.2.2.1
                                              have p19770_3 := h19770c.2.2.2
                                              linarith only [hlam, p19770_0]
                                    · linarith only [h19727, h19763, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h19883 | h19883
                                  · linarith only [h0, h19883, hlam]
                                  · linarith only [h18443, h19883, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h19886 | h19886
                                  · linarith only [h0, h19886, hlam]
                                  · rcases p19747_3 (m.d 0 2) (by simp) with h19888 | h19888
                                    · rcases p19747_3 (m.d 0 3) (by simp) with h19889 | h19889
                                      · linarith only [h19727, h19889, hlam]
                                      · linarith only [h19731, h19889, hlam]
                                    · linarith only [h19729, h19888, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h19893 | h19893
                                  · linarith only [h15532, h19893, hlam]
                                  · rcases p19747_3 (m.d 0 2) (by simp) with h19895 | h19895
                                    · rcases p19747_3 (m.d 0 3) (by simp) with h19896 | h19896
                                      · rcases p19747_3 (m.d 0 4) (by simp) with h19897 | h19897
                                        · linarith only [h19730, h19897, hlam]
                                        · rcases p19747_3 (m.d 0 5) (by simp) with h19899 | h19899
                                          · linarith only [h19731, h19899, hlam]
                                          · linarith only [h18444, h19899, hlam]
                                      · linarith only [h15532, h19896, hlam]
                                    · linarith only [h0, h19895, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h19727, hlam, p19747_1]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h19906 | h19906
                                  · linarith only [h15532, h19906, hlam]
                                  · linarith only [h18443, h19906, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h19909 | h19909
                                  · linarith only [h15532, h19909, hlam]
                                  · rcases p19747_3 (m.d 0 2) (by simp) with h19911 | h19911
                                    · rcases p19747_3 (m.d 0 3) (by simp) with h19912 | h19912
                                      · rcases p19747_3 (m.d 0 4) (by simp) with h19913 | h19913
                                        · linarith only [h19730, h19913, hlam]
                                        · rcases p19747_3 (m.d 0 5) (by simp) with h19915 | h19915
                                          · linarith only [h19731, h19915, hlam]
                                          · rcases h2bigk with h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c | h19917c
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h0, hlam, p19917_1]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              rcases p19917_3 (m.d 0 2) (by simp) with h19920 | h19920
                                              · rcases p19917_3 (m.d 1 2) (by simp) with h19921 | h19921
                                                · rcases p19917_3 (m.d 2 3) (by simp) with h19922 | h19922
                                                  · linarith only [h19922, hlam, p19917_0]
                                                  · rcases p19917_3 (m.d 2 4) (by simp) with h19924 | h19924
                                                    · linarith only [h19728, h19924, hlam]
                                                    · rcases p19917_3 (m.d 2 5) (by simp) with h19926 | h19926
                                                      · linarith only [h19729, h19926, hlam]
                                                      · rcases h3bigk with h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c | h19928c
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h15532, hlam, p19928_1]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          rcases p19928_3 (m.d 0 3) (by simp) with h19931 | h19931
                                                          · rcases p19928_3 (m.d 1 3) (by simp) with h19932 | h19932
                                                            · rcases p19928_3 (m.d 2 3) (by simp) with h19933 | h19933
                                                              · linarith only [h19727, h19933, hlam]
                                                              · rcases p19928_3 (m.d 3 4) (by simp) with h19935 | h19935
                                                                · linarith only [h19730, h19935, hlam]
                                                                · rcases p19928_3 (m.d 3 5) (by simp) with h19937 | h19937
                                                                  · linarith only [h19731, h19937, hlam]
                                                                  · rcases h5bigk with h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c | h19939c
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [hlam, p19939_0]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h18444, hlam, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h15532, h19734, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19747_1, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h15532, h19734, h19745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19732, hlam, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [hlam, p19939_0]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19739, h19742, h19745, hc34, hc45, hlam, hphi, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19739, h19745, hc34, hc45, hlam, hphi, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19739, hlam, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19729, hlam, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19736, hlam, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [hlam, p19939_0]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h0, h19729, h19745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19743, hlam, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19731, hlam, p19939_0]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19738, hlam, p19939_0]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19742, hlam, p19939_0]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [hlam, p19939_0]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19745, hlam, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc34, hc45, hlam, hphi, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc34, hc45, hlam, hphi, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19742, h19745, hc34, hc45, hlam, hphi, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [h19745, hc34, hc45, hlam, hphi, p19939_1]
                                                                    · have p19939_0 := h19939c.1
                                                                      have p19939_1 := h19939c.2.1
                                                                      have p19939_2 := h19939c.2.2.1
                                                                      have p19939_3 := h19939c.2.2.2
                                                                      linarith only [hlam, p19939_0]
                                                            · linarith only [h19734, h19932, hlam]
                                                          · linarith only [h19727, h19931, hlam]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h18443, h18444, h19735, h19741, hlam, p19747_1, p19928_2]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          rcases p19928_3 (m.d 0 3) (by simp) with h19968 | h19968
                                                          · rcases p19928_3 (m.d 1 3) (by simp) with h19969 | h19969
                                                            · rcases p19928_3 (m.d 2 3) (by simp) with h19970 | h19970
                                                              · linarith only [h19727, h19970, hlam]
                                                              · linarith only [h19742, h19970, hlam]
                                                            · linarith only [h19738, h19969, hlam]
                                                          · linarith only [h19968, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h18443, h18444, h19734, h19735, h19741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p19928_1]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          rcases p19928_3 (m.d 0 3) (by simp) with h19977 | h19977
                                                          · linarith only [h15532, h19977, hlam]
                                                          · linarith only [h19727, h19977, hlam]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h15532, h18443, h18444, h19735, h19741, hlam, p19747_1, p19928_2]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          rcases p19928_3 (m.d 0 3) (by simp) with h19981 | h19981
                                                          · linarith only [h15532, h19981, hlam]
                                                          · linarith only [h19731, h19981, hlam]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19727, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19734, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19917_1, p19928_1]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19917_1, p19928_1]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19730, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19737, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19741, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19745, hlam, p19928_1]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19731, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19738, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19742, hlam, p19928_0]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [h19731, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p19747_1, p19928_1]
                                                        · have p19928_0 := h19928c.1
                                                          have p19928_1 := h19928c.2.1
                                                          have p19928_2 := h19928c.2.2.1
                                                          have p19928_3 := h19928c.2.2.2
                                                          linarith only [hlam, p19928_0]
                                                · linarith only [h19734, h19921, hlam]
                                              · linarith only [h19920, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h18443, h18444, h19727, h19735, hlam, p19747_1, p19917_2]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              rcases p19917_3 (m.d 0 2) (by simp) with h20002 | h20002
                                              · rcases p19917_3 (m.d 1 2) (by simp) with h20003 | h20003
                                                · rcases p19917_3 (m.d 2 3) (by simp) with h20004 | h20004
                                                  · linarith only [h19727, h20004, hlam]
                                                  · linarith only [h19742, h20004, hlam]
                                                · linarith only [h19736, h20003, hlam]
                                              · linarith only [h20002, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h18444, h19727, hc01, hc12, hlam, hphi, p19747_1, p19917_1]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              rcases p19917_3 (m.d 0 2) (by simp) with h20011 | h20011
                                              · linarith only [h0, h20011, hlam]
                                              · linarith only [h19727, h20011, hlam]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h0, h18443, h18444, h19727, h19735, hlam, p19747_1, p19917_2]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              rcases p19917_3 (m.d 0 2) (by simp) with h20015 | h20015
                                              · linarith only [h0, h20015, hlam]
                                              · linarith only [h19729, h20015, hlam]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19727, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19734, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              rcases p19917_3 (m.d 0 2) (by simp) with h20021 | h20021
                                              · rcases p19917_3 (m.d 1 2) (by simp) with h20022 | h20022
                                                · rcases p19917_3 (m.d 2 3) (by simp) with h20023 | h20023
                                                  · rcases p19917_3 (m.d 2 4) (by simp) with h20024 | h20024
                                                    · linarith only [h19741, h20024, hlam]
                                                    · rcases p19917_3 (m.d 2 5) (by simp) with h20026 | h20026
                                                      · linarith only [h19742, h20026, hlam]
                                                      · linarith only [h19743, h20026, hlam]
                                                  · linarith only [h19741, h20023, hlam]
                                                · linarith only [h19735, h20022, hlam]
                                              · linarith only [h19728, h20021, hlam]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              rcases p19917_3 (m.d 0 2) (by simp) with h20032 | h20032
                                              · rcases p19917_3 (m.d 1 2) (by simp) with h20033 | h20033
                                                · rcases p19917_3 (m.d 2 3) (by simp) with h20034 | h20034
                                                  · rcases p19917_3 (m.d 2 4) (by simp) with h20035 | h20035
                                                    · linarith only [h19741, h20035, hlam]
                                                    · rcases p19917_3 (m.d 2 5) (by simp) with h20037 | h20037
                                                      · linarith only [h19742, h20037, hlam]
                                                      · rcases h3bigk with h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c | h20039c
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h15532, hlam, p20039_1]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19727, h19741, h19743, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p19917_1, p20039_1]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h18443, h18444, h19735, h19741, hlam, p19747_1, p20039_2]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          rcases p20039_3 (m.d 0 3) (by simp) with h20044 | h20044
                                                          · rcases p20039_3 (m.d 1 3) (by simp) with h20045 | h20045
                                                            · rcases p20039_3 (m.d 2 3) (by simp) with h20046 | h20046
                                                              · linarith only [h19727, h20046, hlam]
                                                              · linarith only [h19742, h20046, hlam]
                                                            · linarith only [h19738, h20045, hlam]
                                                          · linarith only [h20044, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h18443, h18444, h19734, h19735, h19741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p20039_1]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19734, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p19917_1, p20039_1]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h15532, h18443, h18444, h19735, h19741, hlam, p19747_1, p20039_2]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          rcases p20039_3 (m.d 0 3) (by simp) with h20055 | h20055
                                                          · linarith only [h15532, h20055, hlam]
                                                          · linarith only [h19731, h20055, hlam]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19727, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19734, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          rcases p20039_3 (m.d 0 3) (by simp) with h20061 | h20061
                                                          · rcases p20039_3 (m.d 1 3) (by simp) with h20062 | h20062
                                                            · rcases p20039_3 (m.d 2 3) (by simp) with h20063 | h20063
                                                              · rcases p20039_3 (m.d 3 4) (by simp) with h20064 | h20064
                                                                · linarith only [h20064, hlam, p20039_0]
                                                                · rcases p20039_3 (m.d 3 5) (by simp) with h20066 | h20066
                                                                  · linarith only [h19742, h20066, hlam]
                                                                  · linarith only [h19745, h20066, hlam]
                                                              · linarith only [h20063, hlam, p20039_0]
                                                            · linarith only [h19737, h20062, hlam]
                                                          · linarith only [h19730, h20061, hlam]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          rcases p20039_3 (m.d 0 3) (by simp) with h20072 | h20072
                                                          · rcases p20039_3 (m.d 1 3) (by simp) with h20073 | h20073
                                                            · rcases p20039_3 (m.d 2 3) (by simp) with h20074 | h20074
                                                              · rcases p20039_3 (m.d 3 4) (by simp) with h20075 | h20075
                                                                · linarith only [h19741, h20075, hlam]
                                                                · rcases p20039_3 (m.d 3 5) (by simp) with h20077 | h20077
                                                                  · linarith only [h20077, hlam, p20039_0]
                                                                  · rcases h5bigk with h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c | h20079c
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [hlam, p20079_0]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h18444, hlam, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [hc03, hc25, hlam, hphi, ht0b, ht5b, p19747_1, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h0, h19727, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19747_1, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19732, hlam, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [hlam, p20079_0]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19739, h19741, h19743, hc34, hc45, hlam, hphi, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19739, h19745, hc34, hc45, hlam, hphi, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19739, hlam, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19729, hlam, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19736, hlam, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [hlam, p20079_0]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p19917_1, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19743, hlam, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19731, hlam, p20079_0]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19738, hlam, p20079_0]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19742, hlam, p20079_0]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [hlam, p20079_0]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19745, hlam, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc34, hc45, hlam, hphi, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h18443, h18444, h19735, h19741, hc34, hc45, hlam, hphi, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19741, h19743, hc34, hc45, hlam, hphi, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [h19745, hc34, hc45, hlam, hphi, p20079_1]
                                                                    · have p20079_0 := h20079c.1
                                                                      have p20079_1 := h20079c.2.1
                                                                      have p20079_2 := h20079c.2.2.1
                                                                      have p20079_3 := h20079c.2.2.2
                                                                      linarith only [hlam, p20079_0]
                                                              · linarith only [h20074, hlam, p20039_0]
                                                            · linarith only [h19738, h20073, hlam]
                                                          · linarith only [h19731, h20072, hlam]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19730, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19737, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19741, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19745, hlam, p20039_1]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19731, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19738, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h19742, hlam, p20039_0]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [h0, h19727, h19731, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p20039_1]
                                                        · have p20039_0 := h20039c.1
                                                          have p20039_1 := h20039c.2.1
                                                          have p20039_2 := h20039c.2.2.1
                                                          have p20039_3 := h20039c.2.2.2
                                                          linarith only [hlam, p20039_0]
                                                  · linarith only [h19742, h20034, hlam]
                                                · linarith only [h19736, h20033, hlam]
                                              · linarith only [h19729, h20032, hlam]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19728, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19735, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19741, hlam, p19917_1]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19743, hlam, p19917_1]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19729, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19736, hlam, p19917_0]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h19742, hlam, p19917_1]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [h0, h19727, h19729, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p19747_1, p19917_1]
                                            · have p19917_0 := h19917c.1
                                              have p19917_1 := h19917c.2.1
                                              have p19917_2 := h19917c.2.2.1
                                              have p19917_3 := h19917c.2.2.2
                                              linarith only [hlam, p19917_0]
                                      · linarith only [h19731, h19912, hlam]
                                    · linarith only [h19729, h19911, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h18443, hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h19728, hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h19730, hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h19732, hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h18443, h19732, hc14, hc45, hlam, hphi, p19747_1]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h19729, hlam, p19747_1]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [h19731, hlam, p19747_0]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  rcases p19747_3 (m.d 0 1) (by simp) with h20141 | h20141
                                  · linarith only [h18444, h20141, hlam]
                                  · linarith only [h18443, h20141, hlam]
                                · have p19747_0 := h19747c.1
                                  have p19747_1 := h19747c.2.1
                                  have p19747_2 := h19747c.2.2.1
                                  have p19747_3 := h19747c.2.2.2
                                  linarith only [hlam, p19747_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20145 | h20145
                            · linarith only [h18443, h18444, h19735, h19739, h20145, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20147 | h20147
                              · linarith only [h18444, h19727, h19731, h19739, h19741, h19742, h20147, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases h0bigk with h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c | h20149c
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h0, hlam, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h15532, hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h18444, h19739, hc04, hc45, hlam, hphi, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h18444, hlam, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  rcases p20149_3 (m.d 0 1) (by simp) with h20155 | h20155
                                  · linarith only [h0, h20155, hlam]
                                  · rcases p20149_3 (m.d 0 2) (by simp) with h20157 | h20157
                                    · rcases p20149_3 (m.d 0 3) (by simp) with h20158 | h20158
                                      · linarith only [h19727, h20158, hlam]
                                      · linarith only [h15532, h20158, hlam]
                                    · linarith only [h0, h20157, hlam]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h0, h19731, h19742, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  rcases p20149_3 (m.d 0 1) (by simp) with h20164 | h20164
                                  · linarith only [h0, h20164, hlam]
                                  · linarith only [h18443, h20164, hlam]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h0, h19731, h19741, h19742, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  rcases p20149_3 (m.d 0 1) (by simp) with h20168 | h20168
                                  · linarith only [h15532, h20168, hlam]
                                  · rcases p20149_3 (m.d 0 2) (by simp) with h20170 | h20170
                                    · rcases p20149_3 (m.d 0 3) (by simp) with h20171 | h20171
                                      · rcases p20149_3 (m.d 0 4) (by simp) with h20172 | h20172
                                        · linarith only [h19730, h20172, hlam]
                                        · rcases p20149_3 (m.d 0 5) (by simp) with h20174 | h20174
                                          · linarith only [h19731, h20174, hlam]
                                          · linarith only [h18444, h20174, hlam]
                                      · linarith only [h15532, h20171, hlam]
                                    · linarith only [h0, h20170, hlam]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h19727, hlam, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  rcases p20149_3 (m.d 0 1) (by simp) with h20181 | h20181
                                  · linarith only [h15532, h20181, hlam]
                                  · linarith only [h18443, h20181, hlam]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h0, h19727, h19731, h19741, h19742, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h18443, hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h19728, hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h19730, hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h19732, hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h18443, h18444, h19735, h19739, h19741, hc34, hc45, hlam, hphi, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h19729, hlam, p20149_1]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [h19731, hlam, p20149_0]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  rcases p20149_3 (m.d 0 1) (by simp) with h20193 | h20193
                                  · linarith only [h18444, h20193, hlam]
                                  · linarith only [h18443, h20193, hlam]
                                · have p20149_0 := h20149c.1
                                  have p20149_1 := h20149c.2.1
                                  have p20149_2 := h20149c.2.2.1
                                  have p20149_3 := h20149c.2.2.2
                                  linarith only [hlam, p20149_0]
                        · linarith only [h18443, h18444, h19737, h19739, h19741, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h15532, h19731, h19738, hlam]
                  · linarith only [h15532, h19730, h19737, hlam]
                · linarith only [h0, h19729, h19736, hlam]
              · linarith only [h0, h19728, h19735, hlam]
            · linarith only [h0, h19727, h19734, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20203 | h20203
          · linarith only [h15532, h18443, h19731, h20203, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20205 | h20205
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20206 | h20206
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20207 | h20207
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20208 | h20208
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20209 | h20209
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20210 | h20210
                      · linarith only [h15532, h18443, h19731, h20203, h20205, h20209, h20210, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20212 | h20212
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20213 | h20213
                          · linarith only [h15532, h18443, h19727, h19731, h20213, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20215 | h20215
                            · linarith only [h15532, h18443, h19731, h20206, h20209, h20210, h20215, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20217 | h20217
                              · linarith only [h15532, h18443, h19731, h20206, h20209, h20210, h20212, h20217, hlam]
                              · rcases h0bigk with h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c | h20219c
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h0, hlam, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h15532, hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h15532, h18443, h19731, h20205, h20206, h20209, h20212, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h18444, hlam, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  rcases p20219_3 (m.d 0 1) (by simp) with h20225 | h20225
                                  · linarith only [h0, h20225, hlam]
                                  · rcases p20219_3 (m.d 0 2) (by simp) with h20227 | h20227
                                    · rcases p20219_3 (m.d 0 3) (by simp) with h20228 | h20228
                                      · linarith only [h19727, h20228, hlam]
                                      · linarith only [h15532, h20228, hlam]
                                    · linarith only [h0, h20227, hlam]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  rcases p20219_3 (m.d 0 1) (by simp) with h20233 | h20233
                                  · linarith only [h0, h20233, hlam]
                                  · rcases p20219_3 (m.d 0 2) (by simp) with h20235 | h20235
                                    · rcases p20219_3 (m.d 0 3) (by simp) with h20236 | h20236
                                      · linarith only [h19727, h20236, hlam]
                                      · rcases p20219_3 (m.d 0 4) (by simp) with h20238 | h20238
                                        · linarith only [h19728, h20238, hlam]
                                        · rcases p20219_3 (m.d 0 5) (by simp) with h20240 | h20240
                                          · linarith only [h19729, h20240, hlam]
                                          · linarith only [h19731, h20240, hlam]
                                    · linarith only [h19727, h20235, hlam]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  rcases p20219_3 (m.d 0 1) (by simp) with h20244 | h20244
                                  · linarith only [h0, h20244, hlam]
                                  · linarith only [h18443, h20244, hlam]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  rcases p20219_3 (m.d 0 1) (by simp) with h20247 | h20247
                                  · linarith only [h0, h20247, hlam]
                                  · rcases p20219_3 (m.d 0 2) (by simp) with h20249 | h20249
                                    · rcases p20219_3 (m.d 0 3) (by simp) with h20250 | h20250
                                      · linarith only [h19727, h20250, hlam]
                                      · rcases p20219_3 (m.d 0 4) (by simp) with h20252 | h20252
                                        · linarith only [h19728, h20252, hlam]
                                        · rcases p20219_3 (m.d 0 5) (by simp) with h20254 | h20254
                                          · linarith only [h19729, h20254, hlam]
                                          · rcases h2bigk with h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c | h20256c
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h0, hlam, p20256_1]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              rcases p20256_3 (m.d 0 2) (by simp) with h20259 | h20259
                                              · rcases p20256_3 (m.d 1 2) (by simp) with h20260 | h20260
                                                · rcases p20256_3 (m.d 2 3) (by simp) with h20261 | h20261
                                                  · linarith only [h20261, hlam, p20256_0]
                                                  · rcases p20256_3 (m.d 2 4) (by simp) with h20263 | h20263
                                                    · linarith only [h19728, h20263, hlam]
                                                    · rcases p20256_3 (m.d 2 5) (by simp) with h20265 | h20265
                                                      · linarith only [h19729, h20265, hlam]
                                                      · linarith only [h20213, h20265, hlam]
                                                · linarith only [h20205, h20260, hlam]
                                              · linarith only [h20259, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h15532, h18443, h19731, h20206, hlam, p20219_1, p20256_2]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              rcases p20256_3 (m.d 0 2) (by simp) with h20271 | h20271
                                              · rcases p20256_3 (m.d 1 2) (by simp) with h20272 | h20272
                                                · rcases p20256_3 (m.d 2 3) (by simp) with h20273 | h20273
                                                  · linarith only [h19727, h20273, hlam]
                                                  · rcases p20256_3 (m.d 2 4) (by simp) with h20275 | h20275
                                                    · linarith only [h19728, h20275, hlam]
                                                    · rcases p20256_3 (m.d 2 5) (by simp) with h20277 | h20277
                                                      · linarith only [h20277, hlam, p20256_0]
                                                      · rcases h3bigk with h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c | h20279c
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h15532, hlam, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h0, h19731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20219_1, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h0, h19731, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20219_1, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h19731, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          rcases p20279_3 (m.d 0 3) (by simp) with h20285 | h20285
                                                          · linarith only [h15532, h20285, hlam]
                                                          · rcases p20279_3 (m.d 1 3) (by simp) with h20287 | h20287
                                                            · rcases p20279_3 (m.d 2 3) (by simp) with h20288 | h20288
                                                              · linarith only [h20205, h20288, hlam]
                                                              · rcases p20279_3 (m.d 3 4) (by simp) with h20290 | h20290
                                                                · linarith only [h20208, h20290, hlam]
                                                                · rcases p20279_3 (m.d 3 5) (by simp) with h20292 | h20292
                                                                  · linarith only [h20209, h20292, hlam]
                                                                  · linarith only [h19731, h20292, hlam]
                                                            · linarith only [h15532, h20287, hlam]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          rcases p20279_3 (m.d 0 3) (by simp) with h20297 | h20297
                                                          · linarith only [h15532, h20297, hlam]
                                                          · linarith only [h19727, h20297, hlam]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h19727, h19731, h20209, h20212, hlam, p20279_2]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h15532, h19731, hc01, hc13, hlam, hphi, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h19727, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h20205, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h19727, h19731, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p20219_1, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h20213, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h19730, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h20208, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h20212, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h20217, hlam, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h15532, h20205, h20209, hc01, hc12, hlam, hphi, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h20209, hlam, p20279_0]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [h20209, h20210, h20212, hc34, hc45, hlam, hphi, p20279_1]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          rcases p20279_3 (m.d 0 3) (by simp) with h20315 | h20315
                                                          · linarith only [h19731, h20315, hlam]
                                                          · linarith only [h19730, h20315, hlam]
                                                        · have p20279_0 := h20279c.1
                                                          have p20279_1 := h20279c.2.1
                                                          have p20279_2 := h20279c.2.2.1
                                                          have p20279_3 := h20279c.2.2.2
                                                          linarith only [hlam, p20279_0]
                                                · linarith only [h20207, h20272, hlam]
                                              · linarith only [h20271, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h15532, h18443, h19731, h20206, h20212, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20219_1, p20256_1]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              rcases p20256_3 (m.d 0 2) (by simp) with h20323 | h20323
                                              · linarith only [h0, h20323, hlam]
                                              · linarith only [h19727, h20323, hlam]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h0, h15532, h18443, h19731, h20206, hlam, p20219_1, p20256_2]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              rcases p20256_3 (m.d 0 2) (by simp) with h20327 | h20327
                                              · linarith only [h0, h20327, hlam]
                                              · linarith only [h19729, h20327, hlam]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h19727, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h20205, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h19727, h19731, h20212, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p20219_1, p20256_1]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h20213, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h19728, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h20206, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h20212, hlam, p20256_1]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h20215, hlam, p20256_1]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h19729, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h20207, hlam, p20256_0]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h0, h19729, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p20219_1, p20256_1]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [h0, h19729, h20212, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20219_1, p20256_1]
                                            · have p20256_0 := h20256c.1
                                              have p20256_1 := h20256c.2.1
                                              have p20256_2 := h20256c.2.2.1
                                              have p20256_3 := h20256c.2.2.2
                                              linarith only [hlam, p20256_0]
                                    · linarith only [h19729, h20249, hlam]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h18443, h18444, h19731, h20206, h20210, h20212, hc34, hc45, hlam, hphi, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h19727, hlam, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h19731, h20205, h20209, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h19731, hlam, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h18443, hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h19728, hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h19730, hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h20203, hlam, p20219_0]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h18443, h18444, h20206, h20210, h20212, hc34, hc45, hlam, hphi, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h19729, hlam, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [h15532, h18443, h19731, h20205, h20206, h20209, h20212, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20219_1]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  rcases p20219_3 (m.d 0 1) (by simp) with h20359 | h20359
                                  · linarith only [h18444, h20359, hlam]
                                  · linarith only [h18443, h20359, hlam]
                                · have p20219_0 := h20219c.1
                                  have p20219_1 := h20219c.2.1
                                  have p20219_2 := h20219c.2.2.1
                                  have p20219_3 := h20219c.2.2.2
                                  linarith only [hlam, p20219_0]
                        · linarith only [h19730, h19731, h20205, h20209, h20212, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20364 | h20364
                      · linarith only [h15532, h18443, h20203, h20209, h20364, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20366 | h20366
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20367 | h20367
                          · linarith only [h15532, h18443, h20206, h20209, h20366, h20367, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20369 | h20369
                            · linarith only [h15532, h18443, h20206, h20209, h20364, h20369, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20371 | h20371
                              · linarith only [h15532, h18443, h20206, h20209, h20364, h20366, h20371, hlam]
                              · linarith only [h15532, h18443, h20206, h20209, h20366, h20371, hc34, hc45, hlam, hphi]
                        · linarith only [h15532, h19730, h20209, h20366, hc23, hc35, hlam, hphi]
                  · linarith only [h15532, h18443, h19730, h20208, hlam]
                · linarith only [h0, h19729, h20207, hlam]
              · linarith only [h0, h19728, h20206, hlam]
            · linarith only [h0, h19727, h20205, hlam]
      · linarith only [h15532, h18443, h19730, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h20380 | h20380
      · rcases m.htr 0 3 5 (by decide) (by decide) with h20381 | h20381
        · linarith only [h19727, h19729, h20381, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20383 | h20383
          · linarith only [h0, h18443, h19729, h20383, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20385 | h20385
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20386 | h20386
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20387 | h20387
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20388 | h20388
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20389 | h20389
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20390 | h20390
                      · linarith only [h15532, h18443, h19727, h19729, h20383, h20387, h20390, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20392 | h20392
                        · linarith only [h19727, h19729, h20387, h20392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h19727, h19729, h20380, h20387, h20392, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20395 | h20395
                      · linarith only [h15532, h18443, h19727, h19729, h20387, h20395, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20397 | h20397
                        · linarith only [h19727, h19729, h20387, h20397, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h19727, h19729, h20380, h20387, h20397, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h15532, h18443, h20380, h20388, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20401 | h20401
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20402 | h20402
                    · linarith only [h15532, h18443, h20381, h20385, h20386, h20387, h20402, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20404 | h20404
                      · linarith only [h0, h18443, h20387, h20404, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20406 | h20406
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20407 | h20407
                          · linarith only [h0, h19727, h20387, h20402, h20407, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20409 | h20409
                            · linarith only [h0, h18443, h20386, h20387, h20404, h20407, h20409, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h15532, h18443, h20385, h20387, h20409, hc14, hc45, hlam, hphi]
                        · linarith only [h15532, h20380, h20402, h20406, hc23, hc35, hlam, hphi]
                  · linarith only [h15532, h18443, h20380, h20401, hlam]
              · linarith only [h0, h19728, h20386, hlam]
            · linarith only [h0, h19727, h20385, hlam]
      · linarith only [h15532, h18443, h20380, hlam]
  · linarith only [h0, h18443, h19728, hlam]

end R2N4
