import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12840000 in
set_option maxHeartbeats 12840000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_14_H_I_L_I_L_I_s1 m hb0 hb2 hb4 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h5693 | h5693
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5694 | h5694
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5695 | h5695
        · linarith only [h0, h1, h5695, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5697 | h5697
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5698 | h5698
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5699 | h5699
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5700 | h5700
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5701 | h5701
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5702 | h5702
                    · linarith only [h0, h1, h5695, h5697, h5702, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5704 | h5704
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5705 | h5705
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5706 | h5706
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5707 | h5707
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5708 | h5708
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5709 | h5709
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5710 | h5710
                                  · linarith only [h0, h1, h5702, h5704, h5710, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h1, h5702, h5704, h5707, h5710, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h1, h5702, h5709, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h5702, h5708, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5715 | h5715
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5716 | h5716
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5717 | h5717
                                  · linarith only [h5704, h5707, h5717, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5719 | h5719
                                    · linarith only [h5704, h5707, h5715, h5719, hlam]
                                    · rcases h0bigk with h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c | h5721c
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5697, h5701, h5704, h5707, h5715, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h1, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h1, h5701, h5702, h5704, h5707, h5715, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h1, h5702, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h0, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5695, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5701, h5704, h5707, h5715, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h0, h1, h5694, h5702, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h1, h5702, hc01, hc23, hlam, hphi, ht12, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h1, h5702, hc02, hc23, hlam, hphi, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h1, h5701, h5702, h5704, h5707, h5715, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h1, h5701, h5702, h5704, h5707, h5715, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5693, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5697, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5699, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h0, h5697, h5701, h5704, h5707, h5715, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5694, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5698, hlam, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5700, hlam, p5721_0]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [h5701, hlam, p5721_1]
                                      · have p5721_0 := h5721c.1
                                        have p5721_1 := h5721c.2.1
                                        have p5721_2 := h5721c.2.2.1
                                        have p5721_3 := h5721c.2.2.2
                                        linarith only [hlam, p5721_0]
                                · linarith only [h0, h1, h5702, h5716, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h5702, h5715, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1, h5697, h5699, h5706, hlam]
                        · linarith only [h0, h1, h5698, h5704, h5705, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h5697, h5702, h5704, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5752 | h5752
                    · linarith only [h0, h1, h5695, h5752, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5754 | h5754
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5755 | h5755
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5756 | h5756
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5757 | h5757
                            · linarith only [h5693, h5701, h5757, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5759 | h5759
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5760 | h5760
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5761 | h5761
                                  · linarith only [h0, h1, h5701, h5752, h5754, h5761, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5763 | h5763
                                    · linarith only [h5693, h5701, h5754, h5759, h5763, hlam]
                                    · rcases h0bigk with h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c | h5765c
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h1, h5752, hc02, hc23, hlam, hphi, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h1, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h1, h5752, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h1, h5752, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h0, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5695, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h0, h1, h5693, h5752, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h0, h1, h5694, h5752, h5757, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h1, h5752, hc01, hc23, hlam, hphi, ht12, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h1, h5752, hc02, hc23, hlam, hphi, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        rcases p5765_3 (m.d 0 1) (by simp) with h5779 | h5779
                                        · linarith only [h1, h5779, hlam]
                                        · linarith only [h5693, h5779, hlam]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        rcases p5765_3 (m.d 0 1) (by simp) with h5782 | h5782
                                        · linarith only [h1, h5782, hlam]
                                        · linarith only [h5694, h5782, hlam]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5693, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5697, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5699, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5701, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5694, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5698, hlam, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h5700, hlam, p5765_0]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [h1, h5693, h5694, h5752, h5754, h5759, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5765_1]
                                      · have p5765_0 := h5765c.1
                                        have p5765_1 := h5765c.2.1
                                        have p5765_2 := h5765c.2.2.1
                                        have p5765_3 := h5765c.2.2.2
                                        linarith only [hlam, p5765_0]
                                · linarith only [h0, h1, h5752, h5760, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h5752, h5754, h5759, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5699, h5754, h5756, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1, h5698, h5754, h5755, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h5697, h5752, h5754, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h5698, h5700, hlam]
              · linarith only [h1, h5693, h5699, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5802 | h5802
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5803 | h5803
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5804 | h5804
                  · linarith only [h5697, h5698, h5804, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5806 | h5806
                    · linarith only [h0, h1, h5695, h5697, h5806, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5808 | h5808
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5809 | h5809
                        · linarith only [h0, h5698, h5809, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5811 | h5811
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5812 | h5812
                            · linarith only [h1, h5693, h5804, h5806, h5812, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5814 | h5814
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5815 | h5815
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5816 | h5816
                                  · linarith only [h1, h5694, h5804, h5806, h5808, h5809, h5816, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5818 | h5818
                                    · linarith only [h1, h5693, h5698, h5808, h5814, h5816, h5818, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases h0bigk with h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c | h5820c
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h0, h1, h5806, h5808, h5814, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h1, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h1, h5806, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h0, h1, h5698, h5806, h5808, h5814, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h0, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5695, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5693, h5698, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5698, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h1, h5806, hc01, hc23, hlam, hphi, ht12, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h1, h5806, hc02, hc23, hlam, hphi, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        rcases p5820_3 (m.d 0 1) (by simp) with h5834 | h5834
                                        · linarith only [h1, h5834, hlam]
                                        · linarith only [h5693, h5834, hlam]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h0, h1, h5698, h5806, h5808, h5814, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5693, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5697, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5802, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5804, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5694, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h0, h5808, h5814, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h5803, hlam, p5820_0]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [h1, h5693, h5694, h5806, h5808, h5814, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5820_1]
                                      · have p5820_0 := h5820c.1
                                        have p5820_1 := h5820c.2.1
                                        have p5820_2 := h5820c.2.2.1
                                        have p5820_3 := h5820c.2.2.2
                                        linarith only [hlam, p5820_0]
                                · linarith only [h1, h5694, h5803, h5806, h5815, hlam]
                              · linarith only [h0, h1, h5806, h5814, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h5694, h5802, h5808, h5809, h5811, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h5695, h5697, h5808, hc12, hc23, hlam, hphi]
                · linarith only [h1, h5694, h5803, hlam]
              · linarith only [h1, h5694, h5697, h5698, h5802, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5854 | h5854
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5855 | h5855
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5856 | h5856
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5857 | h5857
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5858 | h5858
                    · linarith only [h0, h1, h5695, h5854, h5858, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5860 | h5860
                      · linarith only [h0, h5697, h5860, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5862 | h5862
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5863 | h5863
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5864 | h5864
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5865 | h5865
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5866 | h5866
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5867 | h5867
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5868 | h5868
                                    · rcases h0bigk with h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c | h5869c
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h0, h1, h5858, h5862, h5866, h5868, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h1, hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h0, h1, h5697, h5858, h5862, h5866, h5868, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h1, h5858, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h0, hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5695, hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5697, hlam, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5694, h5697, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h1, h5858, hc01, hc23, hlam, hphi, ht12, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h1, h5858, hc02, hc23, hlam, hphi, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h1, h5693, h5858, h5860, h5862, h5866, h5868, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        rcases p5869_3 (m.d 0 1) (by simp) with h5884 | h5884
                                        · linarith only [h1, h5884, hlam]
                                        · linarith only [h5694, h5884, hlam]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5693, hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h0, h5862, h5866, h5868, hc04, hc45, hlam, hphi, ht0b, ht5b, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5855, hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h1, h5693, h5694, h5858, h5862, h5866, h5868, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5694, hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5854, hlam, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5856, hlam, p5869_0]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [h5857, hlam, p5869_1]
                                      · have p5869_0 := h5869c.1
                                        have p5869_1 := h5869c.2.1
                                        have p5869_2 := h5869c.2.2.1
                                        have p5869_3 := h5869c.2.2.2
                                        linarith only [hlam, p5869_0]
                                    · linarith only [h1, h5693, h5858, h5864, h5868, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h1, h5694, h5697, h5858, h5862, h5864, h5866, h5867, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h1, h5693, h5858, h5860, h5866, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h5693, h5858, h5860, h5862, h5865, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h5693, h5857, h5860, h5862, h5864, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h1, h5862, h5863, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h5697, h5854, h5862, hc12, hc24, hlam, hphi]
                  · linarith only [h5697, h5854, h5857, hlam]
                · linarith only [h1, h5693, h5697, h5854, h5856, hlam]
              · linarith only [h1, h5693, h5855, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5907 | h5907
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5908 | h5908
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5909 | h5909
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5910 | h5910
                    · linarith only [h0, h1, h5695, h5910, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5912 | h5912
                      · linarith only [h0, h5697, h5912, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5914 | h5914
                        · linarith only [h0, h5854, h5914, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5916 | h5916
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5917 | h5917
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5918 | h5918
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5919 | h5919
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5920 | h5920
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5921 | h5921
                                    · rcases h0bigk with h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h1, h5910, hc02, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h1, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5854, h5909, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5854, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5695, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5697, hlam, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5854, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5854, h5909, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5854, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5693, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5693, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5907, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5693, h5854, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5694, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h0, h1, h5694, h5910, hc12, hc23, hlam, hphi, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5908, hlam, p5922_0]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [h5909, hlam, p5922_1]
                                      · have p5922_0 := h5922c.1
                                        have p5922_1 := h5922c.2.1
                                        have p5922_2 := h5922c.2.2.1
                                        have p5922_3 := h5922c.2.2.2
                                        linarith only [hlam, p5922_0]
                                    · linarith only [h1, h5693, h5910, h5917, h5921, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h5693, h5697, h5910, h5917, h5920, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h5693, h5697, h5908, h5909, h5910, h5917, h5919, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h1, h5910, h5918, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5693, h5909, h5910, h5912, h5917, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5916, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5954 | h5954
                    · linarith only [h0, h1, h5695, h5954, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5956 | h5956
                      · linarith only [h0, h5697, h5956, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5958 | h5958
                        · linarith only [h0, h5854, h5958, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5960 | h5960
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5961 | h5961
                            · linarith only [h1, h5693, h5909, h5954, h5961, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5963 | h5963
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5964 | h5964
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5965 | h5965
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5966 | h5966
                                    · linarith only [h0, h1, h5697, h5907, h5909, h5954, h5966, hc12, hc23, hlam, hphi]
                                    · rcases h0bigk with h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c | h5968c
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, h1, h5954, hc12, hc23, hlam, hphi, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h1, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, h1, h5697, h5954, hc12, hc23, hlam, hphi, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h1, h5954, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5695, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5697, hlam, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5854, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h1, h5954, hc01, hc23, hlam, hphi, ht12, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, h1, h5954, hc12, hc23, hlam, hphi, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, h1, h5697, h5954, hc12, hc23, hlam, hphi, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, h1, h5854, h5954, hc12, hc23, hlam, hphi, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5693, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, h5909, h5965, hc12, hc24, hlam, hphi, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5907, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5909, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5694, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h0, h1, h5694, h5954, hc12, hc23, hlam, hphi, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h5908, hlam, p5968_0]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [h1, h5694, h5954, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5968_1]
                                      · have p5968_0 := h5968c.1
                                        have p5968_1 := h5968c.2.1
                                        have p5968_2 := h5968c.2.2.1
                                        have p5968_3 := h5968c.2.2.2
                                        linarith only [hlam, p5968_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5994 | h5994
                                    · linarith only [h1, h5694, h5954, h5960, h5961, h5965, h5994, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h0bigk with h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c | h5996c
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h0, h1, h5954, hc12, hc23, hlam, hphi, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h1, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h1, h5954, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h1, h5954, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h0, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5695, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5697, hlam, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5854, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h1, h5954, hc01, hc23, hlam, hphi, ht12, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h0, h1, h5954, hc12, hc23, hlam, hphi, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h0, h1, h5697, h5954, hc12, hc23, hlam, hphi, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h0, h1, h5854, h5954, hc12, hc23, hlam, hphi, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5693, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h0, h1, h5693, h5954, hc12, hc23, hlam, hphi, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5907, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5909, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5694, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h0, h1, h5694, h5954, hc12, hc23, hlam, hphi, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h5908, hlam, p5996_0]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [h1, h5694, h5954, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5996_1]
                                      · have p5996_0 := h5996c.1
                                        have p5996_1 := h5996c.2.1
                                        have p5996_2 := h5996c.2.2.1
                                        have p5996_3 := h5996c.2.2.2
                                        linarith only [hlam, p5996_0]
                                · linarith only [h0, h1, h5954, h5964, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h5694, h5954, h5956, h5961, h5963, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1, h5960, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h5694, h5908, hlam]
              · linarith only [h1, h5693, h5907, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6027 | h6027
        · linarith only [h0, h1, h6027, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6029 | h6029
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6030 | h6030
            · linarith only [h0, h5694, h6030, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6032 | h6032
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6033 | h6033
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6034 | h6034
                  · linarith only [h0, h5694, h6029, h6034, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6036 | h6036
                    · linarith only [h0, h1, h6027, h6036, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6038 | h6038
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6039 | h6039
                        · linarith only [h0, h5694, h6030, h6039, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6041 | h6041
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6042 | h6042
                            · linarith only [h0, h5693, h5694, h6029, h6034, h6042, hlam]
                            · linarith only [h0, h5694, h6038, h6042, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h6038, h6041, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h6029, h6036, h6038, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6047 | h6047
                  · linarith only [h1, h5693, h6033, h6047, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6049 | h6049
                    · linarith only [h0, h1, h6033, h6049, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6051 | h6051
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6052 | h6052
                        · linarith only [h0, h1, h6030, h6033, h6052, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6054 | h6054
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6055 | h6055
                            · linarith only [h1, h5693, h6033, h6047, h6055, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h5694, h6051, h6055, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h6051, h6054, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h6029, h6049, h6051, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h6029, h6032, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6061 | h6061
            · linarith only [h5693, h5694, h6029, h6061, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6063 | h6063
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6064 | h6064
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6065 | h6065
                  · linarith only [h5693, h5694, h6065, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6067 | h6067
                    · linarith only [h0, h1, h6027, h6067, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6069 | h6069
                      · linarith only [h0, h6029, h6069, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6071 | h6071
                        · linarith only [h0, h5694, h6061, h6071, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6073 | h6073
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6074 | h6074
                            · linarith only [h1, h5693, h6029, h6065, h6067, h6074, hc02, hc23, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6076 | h6076
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6077 | h6077
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6078 | h6078
                                  · linarith only [h0, h5694, h6074, h6078, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6080 | h6080
                                    · linarith only [h1, h5693, h6073, h6078, h6080, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h5694, h6071, h6078, hc02, hc45, hlam, hphi, ht23, ht34, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h1, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, h5694, h6029, h6071, h6078, hc12, hc45, hlam, hphi, ht23, ht34, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h5694, hlam, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h6027, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h6029, hlam, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h6061, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h5693, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, h6027, hc12, hc23, hlam, hphi, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, h6027, h6029, hc12, hc23, hlam, hphi, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, h5694, h6027, hc12, hc23, hlam, hphi, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h5693, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, h5693, h5694, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h6063, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h6065, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h0, h5694, h6071, hc12, hc25, hlam, hphi, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h6064, hlam, p6082_0]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [h5694, h6071, h6078, hc04, hc45, hlam, hphi, p6082_1]
                                      · have p6082_0 := h6082c.1
                                        have p6082_1 := h6082c.2.1
                                        have p6082_2 := h6082c.2.2.1
                                        have p6082_3 := h6082c.2.2.2
                                        linarith only [hlam, p6082_0]
                                · linarith only [h1, h6064, h6067, h6077, hlam]
                              · linarith only [h1, h5693, h6067, h6069, h6076, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h5693, h6069, h6073, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6111 | h6111
                  · linarith only [h5693, h5694, h6111, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6113 | h6113
                    · linarith only [h0, h1, h6064, h6113, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6115 | h6115
                      · linarith only [h0, h1, h6029, h6064, h6115, hc02, hc35, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6117 | h6117
                        · linarith only [h0, h6061, h6117, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6119 | h6119
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6120 | h6120
                            · linarith only [h1, h5693, h6064, h6111, h6120, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6122 | h6122
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6123 | h6123
                                · linarith only [h0, h1, h6064, h6123, hc12, hc23, hlam, hphi]
                                · linarith only [h1, h5693, h6113, h6115, h6123, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h5693, h6113, h6115, h6122, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h5693, h6115, h6119, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h5693, h6063, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h6129 | h6129
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6130 | h6130
        · linarith only [h0, h1, h6130, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6132 | h6132
          · linarith only [h0, h5693, h6132, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6134 | h6134
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6135 | h6135
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6136 | h6136
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6137 | h6137
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6138 | h6138
                    · linarith only [h0, h1, h6130, h6138, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6140 | h6140
                      · linarith only [h0, h5693, h6132, h6140, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6142 | h6142
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6143 | h6143
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6144 | h6144
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6145 | h6145
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6146 | h6146
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6147 | h6147
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6148 | h6148
                                    · rcases h0bigk with h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h5693, h6138, h6143, hc02, hc23, hlam, hphi, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h1, hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h5693, hlam, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h5693, h6138, h6143, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h0, hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h6130, hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h6132, hlam, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h0, h5693, h6129, h6138, h6143, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h0, h6142, h6146, hc03, hc35, hlam, hphi, ht0b, ht5b, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h1, h6138, hc02, hc23, hlam, hphi, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h0, h1, h5693, h6138, h6142, h6146, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        rcases p6149_3 (m.d 0 1) (by simp) with h6164 | h6164
                                        · linarith only [h1, h6164, hlam]
                                        · linarith only [h6129, h6164, hlam]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h0, h6142, h6146, h6148, hc04, hc45, hlam, hphi, ht0b, ht5b, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h0, h5693, h6138, h6142, h6143, h6146, h6148, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h6135, hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        rcases p6149_3 (m.d 0 1) (by simp) with h6171 | h6171
                                        · linarith only [h5693, h6171, hlam]
                                        · linarith only [h6129, h6171, hlam]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h6129, hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h6134, hlam, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h6136, hlam, p6149_0]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [h6137, hlam, p6149_1]
                                      · have p6149_0 := h6149c.1
                                        have p6149_1 := h6149c.2.1
                                        have p6149_2 := h6149c.2.2.1
                                        have p6149_3 := h6149c.2.2.2
                                        linarith only [hlam, p6149_0]
                                    · linarith only [h0, h5693, h6138, h6142, h6143, h6147, h6148, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h5693, h6140, h6147, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h5693, h6138, h6142, h6143, h6146, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h5693, h6138, h6142, h6143, h6145, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h5693, h6142, h6144, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h6135, h6143, hlam]
                        · linarith only [h0, h5693, h6134, h6140, h6142, hc12, hc24, hlam, hphi]
                  · linarith only [h5693, h6129, h6137, hlam]
                · linarith only [h0, h1, h6134, h6136, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6188 | h6188
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6189 | h6189
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6190 | h6190
                    · linarith only [h0, h1, h6130, h6190, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6192 | h6192
                      · linarith only [h0, h6132, h6192, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6194 | h6194
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6195 | h6195
                          · linarith only [h0, h1, h6135, h6190, h6194, h6195, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1, h6194, h6195, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h5693, h6134, h6192, h6194, hc12, hc24, hlam, hphi]
                  · linarith only [h1, h6129, h6135, h6189, hlam]
                · linarith only [h0, h1, h6134, h6188, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6201 | h6201
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6202 | h6202
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6203 | h6203
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6204 | h6204
                    · linarith only [h0, h1, h6130, h6204, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6206 | h6206
                      · linarith only [h0, h5693, h6132, h6206, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6208 | h6208
                        · linarith only [h0, h6134, h6208, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6210 | h6210
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6211 | h6211
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6212 | h6212
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6213 | h6213
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6214 | h6214
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6215 | h6215
                                    · rcases h0bigk with h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c | h6216c
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h5693, h6204, h6210, hc02, hc23, hlam, hphi, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h1, hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h5693, hlam, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h5693, h6204, h6210, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6130, hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6132, hlam, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6134, hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6129, hc03, hc15, hlam, hphi, ht0b, ht5b, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, h1, h6204, hc12, hc23, hlam, hphi, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, h1, h5693, h6204, hc12, hc23, hlam, hphi, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, h1, h6134, h6204, hc12, hc23, hlam, hphi, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, h5693, h6206, hc12, hc24, hlam, hphi, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6201, hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, h1, h6134, h6201, h6204, hc12, hc23, hlam, hphi, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6129, hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h0, h1, h6129, h6204, hc12, hc23, hlam, hphi, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6202, hlam, p6216_0]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [h6203, hlam, p6216_1]
                                      · have p6216_0 := h6216c.1
                                        have p6216_1 := h6216c.2.1
                                        have p6216_2 := h6216c.2.2.1
                                        have p6216_3 := h6216c.2.2.2
                                        linarith only [hlam, p6216_0]
                                    · rcases h0bigk with h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h0, h5693, h6204, h6210, hc12, hc23, hlam, hphi, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h1, hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h5693, hlam, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h5693, h6204, h6210, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h0, hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6130, hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6132, hlam, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6134, hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h1, h6129, h6204, h6211, h6215, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h0, h1, h6204, hc12, hc23, hlam, hphi, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h1, h5693, h6129, h6204, h6211, h6215, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h1, h6129, h6204, h6211, h6215, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6129, h6211, h6215, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h0, h5693, h6204, h6210, hc12, hc23, hlam, hphi, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6201, hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h5693, h6129, h6204, h6210, h6211, h6215, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6129, hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h0, h1, h6129, h6204, hc12, hc23, hlam, hphi, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6202, hlam, p6242_0]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [h6203, hlam, p6242_1]
                                      · have p6242_0 := h6242c.1
                                        have p6242_1 := h6242c.2.1
                                        have p6242_2 := h6242c.2.2.1
                                        have p6242_3 := h6242c.2.2.2
                                        linarith only [hlam, p6242_0]
                                  · linarith only [h0, h5693, h6129, h6132, h6204, h6210, h6211, h6214, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h5693, h6204, h6210, h6213, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h5693, h6129, h6204, h6208, h6210, h6212, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h5693, h6129, h6208, h6211, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h6201, h6210, hlam]
                  · linarith only [h5693, h6129, h6203, hlam]
                · linarith only [h1, h6129, h6202, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6275 | h6275
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6276 | h6276
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6277 | h6277
                    · linarith only [h0, h1, h6201, h6277, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6279 | h6279
                      · linarith only [h0, h1, h6132, h6201, h6279, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6281 | h6281
                        · linarith only [h0, h6134, h6281, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6283 | h6283
                          · linarith only [h0, h1, h6201, h6277, h6283, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h6129, h6281, h6283, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h6129, h6201, h6276, hlam]
                · linarith only [h1, h6129, h6275, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6288 | h6288
        · linarith only [h0, h1, h6288, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6290 | h6290
          · linarith only [h0, h5693, h6290, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6292 | h6292
            · linarith only [h0, h6129, h6292, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6294 | h6294
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6295 | h6295
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6296 | h6296
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6297 | h6297
                    · linarith only [h0, h1, h6288, h6297, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6299 | h6299
                      · linarith only [h0, h1, h6290, h6296, h6297, h6299, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6301 | h6301
                        · linarith only [h0, h6129, h6292, h6301, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6303 | h6303
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6304 | h6304
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6305 | h6305
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6306 | h6306
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6307 | h6307
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6308 | h6308
                                    · rcases h0bigk with h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6129, h6297, h6303, h6304, hc02, hc23, hlam, hphi, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h1, hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h5693, hlam, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6129, hlam, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6288, hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6290, hlam, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6292, hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h1, h6297, hc01, hc23, hlam, hphi, ht12, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, h1, h6297, hc12, hc23, hlam, hphi, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, h1, h6129, h6296, h6297, hc12, hc23, hlam, hphi, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, h1, h6129, h6297, hc12, hc23, hlam, hphi, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, h5693, h6297, h6303, hc12, hc23, hlam, hphi, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6294, hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, h5693, h6129, h6297, h6303, hc12, hc23, hlam, hphi, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h0, h6129, h6297, h6303, h6304, hc12, hc23, hlam, hphi, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6295, hlam, p6309_0]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [h6296, hlam, p6309_1]
                                      · have p6309_0 := h6309c.1
                                        have p6309_1 := h6309c.2.1
                                        have p6309_2 := h6309c.2.2.1
                                        have p6309_3 := h6309c.2.2.2
                                        linarith only [hlam, p6309_0]
                                    · rcases h0bigk with h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, h1, h6297, hc12, hc23, hlam, hphi, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h1, hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h5693, hlam, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h6129, hlam, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h6288, hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h6290, hlam, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h6292, hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h1, h6297, hc01, hc23, hlam, hphi, ht12, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, h1, h6297, hc12, hc23, hlam, hphi, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, h1, h5693, h6297, hc12, hc23, hlam, hphi, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, h1, h6129, h6297, hc12, hc23, hlam, hphi, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, h5693, h6297, h6303, hc12, hc23, hlam, hphi, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h6294, hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, h5693, h6129, h6297, h6303, hc12, hc23, hlam, hphi, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h0, h6129, h6297, h6303, h6304, hc12, hc23, hlam, hphi, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h6295, hlam, p6335_0]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [h6296, hlam, p6335_1]
                                      · have p6335_0 := h6335c.1
                                        have p6335_1 := h6335c.2.1
                                        have p6335_2 := h6335c.2.2.1
                                        have p6335_3 := h6335c.2.2.2
                                        linarith only [hlam, p6335_0]
                                  · linarith only [h0, h5693, h6299, h6307, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h6297, h6306, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h6297, h6305, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h5693, h6296, h6304, hlam]
                          · linarith only [h1, h6294, h6303, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6366 | h6366
                    · linarith only [h0, h5693, h6296, h6366, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6368 | h6368
                      · linarith only [h0, h5693, h6296, h6368, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6370 | h6370
                        · linarith only [h0, h5693, h6292, h6296, h6370, hc02, hc45, hlam, hphi, ht23, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6372 | h6372
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6373 | h6373
                            · linarith only [h0, h5693, h6296, h6366, h6372, h6373, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h5693, h6373, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h6294, h6372, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6377 | h6377
                  · linarith only [h6294, h6295, h6377, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6379 | h6379
                    · linarith only [h0, h1, h6295, h6379, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6381 | h6381
                      · linarith only [h0, h5693, h6377, h6381, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6383 | h6383
                        · linarith only [h0, h1, h6292, h6383, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6385 | h6385
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6386 | h6386
                            · linarith only [h0, h5693, h6377, h6379, h6385, h6386, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h5693, h6386, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h6294, h6295, h6385, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6390 | h6390
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6391 | h6391
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6392 | h6392
                    · linarith only [h0, h1, h6288, h6392, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6394 | h6394
                      · linarith only [h0, h6129, h6290, h6294, h6390, h6394, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6396 | h6396
                        · linarith only [h0, h6129, h6292, h6396, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6398 | h6398
                          · linarith only [h0, h6129, h6294, h6390, h6392, h6398, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6398, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h6294, h6390, h6391, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6402 | h6402
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6403 | h6403
                    · linarith only [h0, h1, h6390, h6403, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6405 | h6405
                      · linarith only [h0, h6290, h6405, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6407 | h6407
                        · linarith only [h0, h6292, h6407, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6409 | h6409
                          · linarith only [h0, h1, h6294, h6403, h6409, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6409, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6412 | h6412
                    · linarith only [h0, h1, h6294, h6402, h6412, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6414 | h6414
                      · linarith only [h0, h1, h6290, h6294, h6402, h6414, hc02, hc45, hlam, hphi, ht23, ht34]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6416 | h6416
                        · linarith only [h0, h1, h6292, h6294, h6402, h6416, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6418 | h6418
                          · linarith only [h0, h1, h6294, h6412, h6418, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6418, hc12, hc34, hlam, hphi, ht23]

end R2N4
